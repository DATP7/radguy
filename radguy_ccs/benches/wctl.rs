use crate::ordered::strategy::BinaryHeapStrategy;
use criterion::BenchmarkId;
use criterion::Criterion;
use criterion::criterion_group;
use criterion::criterion_main;
use orx_priority_queue::DaryHeapWithMap;
use radguy::ordered::strategy::HashMapStrategy;
use radguy::ordered::strategy::OrxStrategy;
use radguy::{
    kleene_local,
    oracle::{
        ArgumentsOracle, IdentityOracle, LocalMaxR, LocalOracle, SMax, TrivialOracle,
        WeightedDepOracle,
    },
    ordered::{
        self,
        oracle::{
            DependencyCountOracle, InverseDependencyCountOracle, SiblingsOracle, SiblingsOracleInv,
            StrategicArgumentsOracle, StrategicLocalOracle, StrategicNonStuckOracle, ToConstant,
            ToOrdered,
        },
        strategy::StrategyWeight,
    },
};

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

            let oracle = $oracle;
            group.bench_with_input(BenchmarkId::new("ordered", format!("{}/{}", $sname, &oracle)), &oracle, |b, o| {
                b.iter_batched(
                    || {
                        (sys.clone(), (*o).clone())
                    },
                    |(mut sys, o)| {
                        let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
                        let target = sys.get_var(process_key, formula_key);
                        let (result, _) = ordered::kleene_local::<_, _, $s, $s, _>(&mut sys, target, &o);
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
                let oracle = $oracle;
                group.bench_with_input(BenchmarkId::new("unordered", &oracle), &oracle, |b, o| {
                    b.iter_batched(
                        || {
                            (sys.clone(), (*o).clone())
                        },
                        |(mut sys, o)| {
                            let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
                            let target = sys.get_var(process_key, formula_key);
                            let (result, _) = kleene_local(&mut sys, target, &o);
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
            IdentityOracle::bitset().ordered(),
            TrivialOracle::bitset().ordered(),

            SMax::bitset().ordered(),
            SMax::bitset().ordered().and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            SMax::bitset().ordered().and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            SMax::bitset().constant(StrategyWeight::Infinity),
            SMax::bitset().constant(StrategyWeight::Infinity).and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            SMax::bitset().constant(StrategyWeight::Infinity).and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            StrategicArgumentsOracle::default(),
            StrategicArgumentsOracle::default().and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            StrategicArgumentsOracle::default().and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min),
            StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min).and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min).and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()),
            StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()).and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()).and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            StrategicArgumentsOracle::default().then(WeightedDepOracle::bitset().ordered()),
            StrategicArgumentsOracle::default().then(WeightedDepOracle::bitset().ordered()).and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            StrategicArgumentsOracle::default().then(WeightedDepOracle::bitset().ordered()).and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min).and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min).and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min).and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min).and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            ArgumentsOracle::bitset().ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::bitset().ordered().then(DependencyCountOracle::default()).and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            ArgumentsOracle::bitset().ordered().then(DependencyCountOracle::default()).and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            ArgumentsOracle::bitset().ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::bitset().ordered().then(InverseDependencyCountOracle::default()).and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            ArgumentsOracle::bitset().ordered().then(InverseDependencyCountOracle::default()).and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            DependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min),
            DependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min).and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            DependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min).and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
            InverseDependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min),
            InverseDependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min).and_by(StrategicNonStuckOracle::bitset(), std::cmp::min),
            InverseDependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min).and_by(StrategicNonStuckOracle::bitset(), std::cmp::max),
        }

        wctl_system_ordered_composed_unordered!(
            $name: using $c, strategy $s; $sname; bench $process_name, $formula_str => $sat in wccs,
            [
                DependencyCountOracle::default(),
                InverseDependencyCountOracle::default(),
                StrategicNonStuckOracle::bitset()
            ]
        );

        wctl_system_ordered_composed_unordered_const_1!(
            $name: using $c, strategy $s; $sname; bench $process_name, $formula_str => $sat in wccs,
            [
                SiblingsOracle,
                SiblingsOracleInv
            ]
        );
    };
}

macro_rules! wctl_bench_suite {
    ($($name:ident: $process_name:expr, $formula_str:expr => $sat:literal in $wccs:expr;)*) => {
        $(
        fn $name(c: &mut Criterion) {
            let wccs = $wccs;
            wctl_bench_oracles_unordered! {
                $name: using c, bench $process_name, $formula_str => $sat in wccs, with
                IdentityOracle::bitset(),
                TrivialOracle::bitset(),
                WeightedDepOracle::bitset(),
                SMax::bitset().then(WeightedDepOracle::bitset()),
                LocalMaxR::bitset().then(WeightedDepOracle::bitset()),
                ArgumentsOracle::bitset().and(SMax::bitset()),
                ArgumentsOracle::bitset().and(LocalMaxR::bitset()),
                SMax::bitset(),
                LocalMaxR::bitset(),
                ArgumentsOracle::bitset(),
                ArgumentsOracle::bitset().then(SMax::bitset()),
                ArgumentsOracle::bitset().then(LocalMaxR::bitset()),
            }
            wctl_bench_problem_ordered!($name: using c, strategy BinaryHeapStrategy<_>; "std_binary"; bench $process_name, $formula_str => $sat in wccs);
            wctl_bench_problem_ordered!($name: using c, strategy HashMapStrategy<_>; "hashmap"; bench $process_name, $formula_str => $sat in wccs);
            wctl_bench_problem_ordered!($name: using c, strategy OrxStrategy<_, DaryHeapWithMap<_, _, 4>>; "orx_quad"; bench $process_name, $formula_str => $sat in wccs);
        }
        )*
        criterion_group!(
            name = benches;
            config = Criterion::default().sample_size(20).measurement_time(std::time::Duration::from_secs(10));
            targets = $($name),*
        );
    };
}

macro_rules! wctl_system_ordered_composed_unordered {
    ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $proc:expr, $formula:expr => $sat:literal in $wccs:expr, [$($strategic_oracle:expr),*]) => {
        $(
            wctl_bench_oracles_ordered! {
                $name: using $c, strategy $s; $sname; bench $proc, $formula => $sat in $wccs, with
                WeightedDepOracle::bitset().ordered().then($strategic_oracle.clone()),
                SMax::bitset().then(WeightedDepOracle::bitset()).ordered().then($strategic_oracle.clone()),
                LocalMaxR::bitset().then(WeightedDepOracle::bitset()).ordered().then($strategic_oracle.clone()),
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

macro_rules! wctl_system_ordered_composed_unordered_const_1 {
    ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $proc:expr, $formula:expr => $sat:literal in $wccs:expr, [$($strategic_oracle:expr),*]) => {
        $(
            wctl_bench_oracles_ordered! {
                $name: using $c, strategy $s; $sname; bench $proc, $formula => $sat in $wccs, with
                WeightedDepOracle::bitset().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                SMax::bitset().then(WeightedDepOracle::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                LocalMaxR::bitset().then(WeightedDepOracle::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                ArgumentsOracle::bitset().and(SMax::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                ArgumentsOracle::bitset().and(LocalMaxR::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                SMax::bitset().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                LocalMaxR::bitset().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                ArgumentsOracle::bitset().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                ArgumentsOracle::bitset().then(SMax::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                ArgumentsOracle::bitset().then(LocalMaxR::bitset()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
            }
        )*
    }
}

wctl_bench_suite! {
    mower_example:
        "S0", "A mow U[<=6] dump" => true
        in r"
        S0 := mow:(<go,2>.S1 + <go,2>.S2 + <go,2>.S3);
        S1 := mow:<go,1>.S4;
        S2 := mow:<go,2>.S4;
        S3 := mow:<go,1>.S5;
        S4 := mow:(<go,0>.S5 + <go,1>.S6);
        S5 := mow:<go,2>.S6;
        S6 := dump:<go,0>.S6;
    ";
    mower_example_neg: "S0", "A mow U[<=4] dump" => false
        in r"
        S0 := mow:(<go,2>.S1 + <go,2>.S2 + <go,2>.S3);
        S1 := mow:<go,1>.S4;
        S2 := mow:<go,2>.S4;
        S3 := mow:<go,1>.S5;
        S4 := mow:(<go,0>.S5 + <go,1>.S6);
        S5 := mow:<go,2>.S6;
        S6 := dump:<go,0>.S6;
    ";
    proposition: "S", "mow" => true in "S := mow:0;";
    proposition_multiple: "S", "mow && dump" => true in "S := mow:dump:0;";
    proposition_multiple_neg: "S", "mow && dump && dud" => false in "S := mow:dump:0;";
    linear_universal_final: "S", "AF dump" => true in "S := <go>.<go>.<go>.<go>.dump:0;";
    recursive: "S", "AF dump" => true in "S := <go>.dump:S;";
    recursive_neg: "S", "AF mow" => false in "S := <go>.dump:S;";
    compare: "S", "mow == 4" => true in "S := mow:0 + mow:0 + mow:0 + mow:0;";
    leader_election: "Ring", "EF leader" => true in include_str!("../systems/wccs/LeaderElection2.wccs");
    leader_election_neg: "Ring", "EF leader > 1" => false in include_str!("../systems/wccs/LeaderElection2.wccs");
}

criterion_main!(benches);
