use crate::ordered::strategy::BinaryHeapStrategy;
use crate::ordered::strategy::StrategyWeight;
use criterion::BenchmarkId;
use criterion::Criterion;
use criterion::criterion_group;
use criterion::criterion_main;
use radguy::{
    kleene_local,
    oracle::{ArgumentsOracle, IdentityOracle, LocalMaxR, LocalOracle, SMax, TrivialOracle},
    ordered::{
        self,
        oracle::{
            ArgumentsStrategy, DependencyCountOracle, StrategicArgumentsOracle,
            StrategicIdentityOracle, StrategicLocalOracle, StrategicNonStuckOracle, ToConstant,
            ToOrdered,
        },
    },
};
use std::{fs::OpenOptions, io::Write, path::Path};

const SKIPPED_PATH: &str = "wctl_skipped_benches.txt";

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

use radguy_ccs::systems::numeric::Number;
use radguy_ccs::systems::wccs;
use radguy_ccs::systems::wccs::wccs_system::WCCSSystem;
use radguy_ccs::systems::wctl;
use radguy_ccs::systems::wctl::wctl_system::WCTLSystem;

macro_rules! wctl_bench_oracles_ordered {
    ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $process_name:expr, $formula_str:expr => $sat:literal in $wccs:expr, with $($oracle:expr,)*) => {{
        let wccs_parser = wccs::ProgramParser::new();
        let wccs_ast = wccs_parser
            .parse(&$wccs)
            .expect("Failed to parse WCCS program content.");

        let formula_parser = wctl::grammar::FormulaParser::new();
        let formula = formula_parser.parse($formula_str).expect("Formula should parse");

        let mut wccs_system = WCCSSystem::<usize>::default();
        wccs_system.insert_ast_bindings(wccs_ast.clone());
        let sys = WCTLSystem::<usize, usize, usize, usize, usize>::new(wccs_system);

        let formula_key = sys.insert_ast_formula(formula.clone());

        let mut group = $c.benchmark_group(stringify!($name));
        $(
        {
            let mut skipped = false;
            let oracle = $oracle;
            group.bench_with_input(BenchmarkId::new("ordered", format!("{}/{}", $sname, &oracle)), &oracle, |b, o| {
                b.iter_batched(
                    || {
                        (sys.clone(), (*o).clone())
                    },
                    |(mut sys, o)| {
                        if skipped {
                            return;
                        }
                        let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
                        let target = sys.get_var(process_key, formula_key);
                        let Some((result, _)) = ordered::kleene_local::<_, _, $s, $s, _>(&mut sys, target, &o) else {
                            skipped = true;
                            append_skipped(&format!("{}/ordered/{}/{}", stringify!($name), $sname, &o));
                            return;
                        };
                        assert_eq!(
                            $sat,
                            result == Number::Val(0),
                            "{} should{} satisfy {} in {} with oracle {}",
                            $process_name,
                            $formula_str,
                            if !$sat { " not" } else { "" },
                            $wccs,
                            o
                        )
                    },
                    criterion::BatchSize::SmallInput,
                );
            });
        }
        )*
    }};
}

macro_rules! wctl_bench_oracles_unordered {
    ($name:ident: using $c:expr, bench $process_name:expr, $formula_str:expr => $sat:literal in $wccs:expr, with $($oracle:expr,)*) => {{
        let wccs_parser = wccs::ProgramParser::new();
        let wccs_ast = wccs_parser
            .parse(&$wccs)
            .expect("Failed to parse WCCS program content.");

        let formula_parser = wctl::grammar::FormulaParser::new();
        let formula = formula_parser.parse($formula_str).expect("Formula should parse");

        let mut group = $c.benchmark_group(stringify!($name));
        $(
            {
                let mut wccs_system = WCCSSystem::<usize>::default();
                wccs_system.insert_ast_bindings(wccs_ast.clone());

                let sys = WCTLSystem::<usize, usize, usize, usize, usize>::new(wccs_system);

                let formula_key = sys.insert_ast_formula(formula.clone());
                let mut skipped = false;
                let oracle = $oracle;
                group.bench_with_input(BenchmarkId::new("unordered", &oracle), &oracle, |b, o| {
                    b.iter_batched(
                        || {
                            (sys.clone(), (*o).clone())
                        },
                        |(mut sys, o)| {
                            if skipped {
                                return;
                            }
                            let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
                            let target = sys.get_var(process_key, formula_key);
                            let Some((result, _)) = kleene_local(&mut sys, target, &o) else {
                                skipped = true;
                                append_skipped(&format!("{}/unordered/{}", stringify!($name), &o));
                                return;
                            };
                            assert_eq!(
                                $sat,
                                result == Number::Val(0),
                                "{} should{} satisfy {} in {} with oracle {}",
                                $process_name,
                                if !$sat { " not" } else { "" },
                                $formula_str,
                                $wccs,
                                o
                            )
                    },
                    criterion::BatchSize::SmallInput,
                );
            });
        }
        )*
    }};
}

macro_rules! wctl_bench_problem_ordered {
    ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $process_name:expr, $formula_str:expr => $sat:literal in $wccs:expr) => {
        let wccs = $wccs;
        wctl_bench_oracles_ordered! {
            $name: using $c, strategy $s; $sname; bench $process_name, $formula_str => $sat in wccs, with
            // StrategicIdentityOracle,
            // IdentityOracle::bitset().ordered(),
            // TrivialOracle::bitset().ordered(),

            // SMax::bitset().ordered(),
            // SMax::bitset().ordered().and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // SMax::bitset().ordered().and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // SMax::bitset().constant(StrategyWeight::Infinity),
            // SMax::bitset().constant(StrategyWeight::Infinity).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // SMax::bitset().constant(StrategyWeight::Infinity).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            StrategicNonStuckOracle::bitset().then(SMax::bitset().ordered()),
            StrategicNonStuckOracle::bitset().then(LocalMaxR::bitset().ordered()),
            // StrategicArgumentsOracle::default(),
            // StrategicArgumentsOracle::default().and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"), // Look here
            // StrategicArgumentsOracle::default().and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min),
            // StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(SMax::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(SMax::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "min"),
            // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()),
            // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).then(SMax::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).then(SMax::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "min"),
            // StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()),
            // StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).then(LocalMaxR::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).then(LocalMaxR::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "min"),
            // StrategicArgumentsOracle::default().and_by(LocalMaxR::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(LocalMaxR::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::default().and_by(LocalMaxR::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).and_by(LocalMaxR::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // StrategicArgumentsOracle::default().then(WeightedDepOracle::bitset().ordered()),
            // StrategicArgumentsOracle::default().then(WeightedDepOracle::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // StrategicArgumentsOracle::default().then(WeightedDepOracle::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min),
            // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // StrategicArgumentsOracle::with(ArgumentsStrategy::Ancestors).then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "min"),
            // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min),
            // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // ArgumentsOracle::bitset().ordered().then(DependencyCountOracle::default()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // ArgumentsOracle::bitset().ordered().then(DependencyCountOracle::default()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // ArgumentsOracle::bitset().ordered().then(InverseDependencyCountOracle::default()),
            // ArgumentsOracle::bitset().ordered().then(InverseDependencyCountOracle::default()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // ArgumentsOracle::bitset().ordered().then(InverseDependencyCountOracle::default()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // DependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min),
            // DependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // DependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),
            // InverseDependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min),
            // InverseDependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            // InverseDependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::max, "max"),

            // Composed ordered
            // WeightedDepOracle::bitset().ordered().then(DependencyCountOracle::default()),
            // SMax::bitset().then(WeightedDepOracle::bitset()).ordered().then(DependencyCountOracle::default()),
            // LocalMaxR::bitset().then(WeightedDepOracle::bitset()).ordered().then(DependencyCountOracle::default()),
            // ArgumentsOracle::bitset().and(SMax::bitset()).ordered().then(DependencyCountOracle::default()),
            // ArgumentsOracle::bitset().and(LocalMaxR::bitset()).ordered().then(DependencyCountOracle::default()),
            // SMax::bitset().ordered().then(DependencyCountOracle::default()),
            // LocalMaxR::bitset().ordered().then(DependencyCountOracle::default()),
            // ArgumentsOracle::bitset().ordered().then(DependencyCountOracle::default()),
            // ArgumentsOracle::bitset().then(SMax::bitset()).ordered().then(DependencyCountOracle::default()),
            // ArgumentsOracle::bitset().then(LocalMaxR::bitset()).ordered().then(DependencyCountOracle::default()),

            // WeightedDepOracle::bitset().ordered().then(InverseDependencyCountOracle::default()),
            // SMax::bitset().then(WeightedDepOracle::bitset()).ordered().then(InverseDependencyCountOracle::default()),
            // LocalMaxR::bitset().then(WeightedDepOracle::bitset()).ordered().then(InverseDependencyCountOracle::default()),
            // ArgumentsOracle::bitset().and(SMax::bitset()).ordered().then(InverseDependencyCountOracle::default()),
            // ArgumentsOracle::bitset().and(LocalMaxR::bitset()).ordered().then(InverseDependencyCountOracle::default()),
            // SMax::bitset().ordered().then(InverseDependencyCountOracle::default()),
            // LocalMaxR::bitset().ordered().then(InverseDependencyCountOracle::default()),
            // ArgumentsOracle::bitset().ordered().then(InverseDependencyCountOracle::default()),
            // ArgumentsOracle::bitset().then(SMax::bitset()).ordered().then(InverseDependencyCountOracle::default()),
            // ArgumentsOracle::bitset().then(LocalMaxR::bitset()).ordered().then(InverseDependencyCountOracle::default()),

            // WeightedDepOracle::bitset().ordered().then(StrategicNonStuckOracle::bitset()),
            // SMax::bitset().then(WeightedDepOracle::bitset()).ordered().then(StrategicNonStuckOracle::bitset()),
            // LocalMaxR::bitset().then(WeightedDepOracle::bitset()).ordered().then(StrategicNonStuckOracle::bitset()),
            // ArgumentsOracle::bitset().and(SMax::bitset()).ordered().then(StrategicNonStuckOracle::bitset()),
            // ArgumentsOracle::bitset().and(LocalMaxR::bitset()).ordered().then(StrategicNonStuckOracle::bitset()),
            // SMax::bitset().ordered().then(StrategicNonStuckOracle::bitset()),
            // LocalMaxR::bitset().ordered().then(StrategicNonStuckOracle::bitset()),
            // ArgumentsOracle::bitset().ordered().then(StrategicNonStuckOracle::bitset()),
            // ArgumentsOracle::bitset().then(SMax::bitset()).ordered().then(StrategicNonStuckOracle::bitset()),
            // ArgumentsOracle::bitset().then(LocalMaxR::bitset()).ordered().then(StrategicNonStuckOracle::bitset()),

            // Composed Siblings
            // WeightedDepOracle::bitset().constant(StrategyWeight::Num(1)).then(SiblingsOracle),
            // SMax::bitset().then(WeightedDepOracle::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracle),
            // LocalMaxR::bitset().then(WeightedDepOracle::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracle),
            // ArgumentsOracle::bitset().and(SMax::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracle),
            // ArgumentsOracle::bitset().and(LocalMaxR::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracle),
            // SMax::bitset().constant(StrategyWeight::Num(1)).then(SiblingsOracle),
            // LocalMaxR::bitset().constant(StrategyWeight::Num(1)).then(SiblingsOracle),
            // ArgumentsOracle::bitset().constant(StrategyWeight::Num(1)).then(SiblingsOracle),
            // ArgumentsOracle::bitset().then(SMax::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracle),
            // ArgumentsOracle::bitset().then(LocalMaxR::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracle),

            // WeightedDepOracle::bitset().constant(StrategyWeight::Num(1)).then(SiblingsOracleInv),
            // SMax::bitset().then(WeightedDepOracle::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracleInv),
            // LocalMaxR::bitset().then(WeightedDepOracle::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracleInv),
            // ArgumentsOracle::bitset().and(SMax::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracleInv),
            // ArgumentsOracle::bitset().and(LocalMaxR::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracleInv),
            // SMax::bitset().constant(StrategyWeight::Num(1)).then(SiblingsOracleInv),
            // LocalMaxR::bitset().constant(StrategyWeight::Num(1)).then(SiblingsOracleInv),
            // ArgumentsOracle::bitset().constant(StrategyWeight::Num(1)).then(SiblingsOracleInv),
            // ArgumentsOracle::bitset().then(SMax::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracleInv),
            // ArgumentsOracle::bitset().then(LocalMaxR::bitset()).constant(StrategyWeight::Num(1)).then(SiblingsOracleInv),
        }
    };
}

macro_rules! wctl_bench_suite {
    ($($name:ident: $process_name:expr, $formula_str:expr => $sat:literal in $wccs:expr;)*) => {
        $(
        fn $name(c: &mut Criterion) {
            let wccs = $wccs;
            // wctl_bench_oracles_unordered! {
            //     $name: using c, bench $process_name, $formula_str => $sat in wccs, with
            //     IdentityOracle::bitset(),
                // TrivialOracle::bitset(),
                // WeightedDepOracle::bitset(),
                // SMax::bitset().then(WeightedDepOracle::bitset()),
                // LocalMaxR::bitset().then(WeightedDepOracle::bitset()),
                // ArgumentsOracle::bitset().and(SMax::bitset()),
                // ArgumentsOracle::bitset().and(LocalMaxR::bitset()),
                // SMax::bitset(),
                // LocalMaxR::bitset(),
                // ArgumentsOracle::bitset(),
                // ArgumentsOracle::bitset().then(SMax::bitset()),
                // ArgumentsOracle::bitset().then(LocalMaxR::bitset()),
            // }
            wctl_bench_problem_ordered!($name: using c, strategy BinaryHeapStrategy<_>; "std_binary"; bench $process_name, $formula_str => $sat in wccs);
            // wctl_bench_problem_ordered!($name: using c, strategy OrxStrategy<_, DaryHeapWithMap<_, _, 4>>; "orx_quad"; bench $process_name, $formula_str => $sat in wccs);
            // wctl_bench_problem_ordered!($name: using c, strategy LazyHeap<_, BinaryHeapStrategy<_>>; "std_binary_lazy"; bench $process_name, $formula_str => $sat in wccs);
            // wctl_bench_problem_ordered!($name: using c, strategy LazyHeap<_, OrxStrategy<_, DaryHeapWithMap<_, _, 4>>>; "orx_quad_lazy"; bench $process_name, $formula_str => $sat in wccs);
        }
        )*
        criterion_group!(
            name = benches;
            config = Criterion::default().sample_size(20).measurement_time(std::time::Duration::from_secs(10));
            targets = $($name),*
        );
    };
}

// macro_rules! wctl_system_ordered_composed_unordered {
//     ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $proc:expr, $formula:expr => $sat:literal in $wccs:expr, [$($strategic_oracle:expr),*]) => {
//         $(
//             wctl_bench_oracles_ordered! {
//                 $name: using $c, strategy $s; $sname; bench $proc, $formula => $sat in $wccs, with
//                 WeightedDepOracle::bitset().ordered().then($strategic_oracle.clone()),
//                 SMax::bitset().then(WeightedDepOracle::bitset()).ordered().then($strategic_oracle.clone()),
//                 LocalMaxR::bitset().then(WeightedDepOracle::bitset()).ordered().then($strategic_oracle.clone()),
//                 ArgumentsOracle::bitset().and(SMax::bitset()).ordered().then($strategic_oracle.clone()),
//                 ArgumentsOracle::bitset().and(LocalMaxR::bitset()).ordered().then($strategic_oracle.clone()),
//                 SMax::bitset().ordered().then($strategic_oracle.clone()),
//                 LocalMaxR::bitset().ordered().then($strategic_oracle.clone()),
//                 ArgumentsOracle::bitset().ordered().then($strategic_oracle.clone()),
//                 ArgumentsOracle::bitset().then(SMax::bitset()).ordered().then($strategic_oracle.clone()),
//                 ArgumentsOracle::bitset().then(LocalMaxR::bitset()).ordered().then($strategic_oracle.clone()),
//             }
//         )*
//     }
// }

// macro_rules! wctl_system_ordered_composed_unordered_const_1 {
//     ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $proc:expr, $formula:expr => $sat:literal in $wccs:expr, [$($strategic_oracle:expr),*]) => {
//         $(
//             wctl_bench_oracles_ordered! {
//                 $name: using $c, strategy $s; $sname; bench $proc, $formula => $sat in $wccs, with
//                 WeightedDepOracle::bitset().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
//                 SMax::bitset().then(WeightedDepOracle::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
//                 LocalMaxR::bitset().then(WeightedDepOracle::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
//                 ArgumentsOracle::bitset().and(SMax::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
//                 ArgumentsOracle::bitset().and(LocalMaxR::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
//                 SMax::bitset().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
//                 LocalMaxR::bitset().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
//                 ArgumentsOracle::bitset().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
//                 ArgumentsOracle::bitset().then(SMax::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
//                 ArgumentsOracle::bitset().then(LocalMaxR::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
//             }
//         )*
//     }
// }

wctl_bench_suite! {
    semaphore_3_5_fail: "System", "EF critical_section > 3" => false in include_str!("../systems/wccs/Semaphore_3_5.wccs");
    semaphore_3_5_succ: "System", "EF critical_section == 3" => true in include_str!("../systems/wccs/Semaphore_3_5.wccs");
    client_server_failed_5: "System", "E True U[<=5] failed" => true in include_str!("../systems/wccs/ClientServer.wccs");
    client_server_deliver_8: "System", "E True U[<=8] delivered" => true in include_str!("../systems/wccs/ClientServer.wccs");
    client_server_big: "System", "E True U[<=10] (A True U[<=1] failed)" => true in include_str!("../systems/wccs/ClientServer.wccs");
    leader_election_6: "Ring", "EF leader" => true in include_str!("../systems/wccs/LeaderElection6.wccs");
    leader_election_neg_6: "Ring", "EF leader > 1" => false in include_str!("../systems/wccs/LeaderElection6.wccs");
    leader_election_7: "Ring", "EF leader" => true in include_str!("../systems/wccs/LeaderElection7.wccs");
    leader_election_neg_7: "Ring", "EF leader > 1" => false in include_str!("../systems/wccs/LeaderElection7.wccs");
    leader_election_8: "Ring", "EF leader" => true in include_str!("../systems/wccs/LeaderElection8.wccs");
    leader_election_neg_8: "Ring", "EF leader > 1" => false in include_str!("../systems/wccs/LeaderElection8.wccs");
}

criterion_main!(benches);
