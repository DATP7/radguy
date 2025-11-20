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
    oracle::SMax,
    ordered::{self, oracle::ToConstant, strategy::StrategyWeight},
};

use radguy_ccs::systems::numeric::Number;
use radguy_ccs::systems::wccs;
use radguy_ccs::systems::wccs::wccs_system::WCCSSystem;
use radguy_ccs::systems::wctl;
use radguy_ccs::systems::wctl::wctl_system::WCTLSystem;
use slotmap::DefaultKey;

macro_rules! wctl_bench_oracles_ordered {
    ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $process_name:expr, $formula_str:expr => $sat:literal in $wccs:expr, with $($oracle:expr,)*) => {{
        let wccs_parser = wccs::ProgramParser::new();
        let wccs_ast = wccs_parser
            .parse(&$wccs)
            .expect("Failed to parse WCCS program content.");

        let formula_parser = wctl::grammar::FormulaParser::new();
        let formula = formula_parser.parse($formula_str).expect("Formula should parse");

        let mut wccs_system = WCCSSystem::<DefaultKey>::default();
        wccs_system.insert_ast_bindings(wccs_ast.clone());
        let sys = WCTLSystem::<DefaultKey, DefaultKey, DefaultKey, DefaultKey, DefaultKey>::new(wccs_system);

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
                        let result = ordered::kleene_local::<_, _, $s, $s, _>(&mut sys, target, &o) == Number::Val(0);
                        assert_eq!(
                            $sat,
                            result,
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

        let mut wccs_system = WCCSSystem::<DefaultKey>::default();
        wccs_system.insert_ast_bindings(wccs_ast.clone());
        let sys = WCTLSystem::<DefaultKey, DefaultKey, DefaultKey, DefaultKey, DefaultKey>::new(wccs_system);

        let formula_key = sys.insert_ast_formula(formula.clone());

        let mut group = $c.benchmark_group(stringify!($name));
        $(
            {
                let oracle = $oracle;
                group.bench_with_input(BenchmarkId::new("unordered", &oracle), &oracle, |b, o| {
                    b.iter_batched(
                        || {
                            (sys.clone(), (*o).clone())
                        },
                        |(mut sys, o)| {
                            let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
                            let target = sys.get_var(process_key, formula_key);
                            let result = kleene_local(&mut sys, target, &o) == Number::Val(0);
                            assert_eq!(
                                $sat,
                                result,
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

macro_rules! wctl_bench_problem_ordered {
    ($name:ident: using $c:expr, strategy $s:ty; $sname:literal; bench $process_name:expr, $formula_str:expr => $sat:literal in $wccs:expr) => {
        let wccs = $wccs;

        wctl_bench_oracles_ordered! {
            $name: using $c, strategy $s; $sname; bench $process_name, $formula_str => $sat in wccs, with
            SMax::default().constant(StrategyWeight::Infinity),
            // LocalMaxR::default().constant(StrategyWeight::Infinity),
            // LocalMaxR::default().constant(StrategyWeight::Infinity).then(CountOracle::default()),
            // LocalMaxR::default().constant(StrategyWeight::Infinity).then(InverseCountOracle::default()),
            // // BoolExtension::oracle().constant(StrategyWeight::Infinity).and_by(InverseCountOracle, std::cmp::min),
            // // BoolExtension::oracle().constant(StrategyWeight::Infinity).and_by(CountOracle, std::cmp::min),
            // StrategicArgumentsOracle::default(),
            // StrategicArgumentsOracle::default().and_by(CountOracle::default(), std::cmp::min),
            // StrategicArgumentsOracle::default().and_by(InverseCountOracle::default(), std::cmp::min),
            // CountOracle::default().then(StrategicArgumentsOracle::default()),
            // InverseCountOracle::default().then(StrategicArgumentsOracle::default()),
            // StrategicArgumentsOracle::default().then(CountOracle::default()),
            // StrategicArgumentsOracle::default().then(InverseCountOracle::default()),
            // StrategicArgumentsOracle::default().and_by(SMax::default().constant(StrategyWeight::Infinity), std::cmp::min).then(CountOracle::default()),
            // StrategicArgumentsOracle::default().and_by(SMax::default().constant(StrategyWeight::Infinity), std::cmp::min).then(InverseCountOracle::default()),
        };
    };
}

macro_rules! wctl_bench_suite_problem {
    ($name:ident: using $c:expr, $process_name:expr, $formula_str:expr => $sat:literal in $wccs:expr) => {
        let wccs = $wccs;
        wctl_bench_oracles_unordered!($name: using $c, bench $process_name, $formula_str => $sat in wccs, with
            SMax::default(),
            // TODO: LocalMaxR and Arguments should be fixed
            // LocalMaxR::default(),
            // ArgumentsOracle::default(),
            // ArgumentsOracle::default().then(SMax::default()),
            // ArgumentsOracle::default().then(LocalMaxR::default()),
            // ArgumentsOracle::default().and(SMax::default()),
            // ArgumentsOracle::default().and(LocalMaxR::default()),
            // BoolExtension::oracle(),
            // SMax::default().then(BoolExtension::oracle()),
            // LocalMaxR::default().then(BoolExtension::oracle()),
        );

        wctl_bench_problem_ordered!($name: using $c, strategy BinaryHeapStrategy<_>; "std_binary"; bench $process_name, $formula_str => $sat in wccs);
        wctl_bench_problem_ordered!($name: using $c, strategy HashMapStrategy<_>; "hashmap"; bench $process_name, $formula_str => $sat in wccs);
        wctl_bench_problem_ordered!($name: using $c, strategy OrxStrategy<_, DaryHeapWithMap<_, _, 4>>; "orx_quad"; bench $process_name, $formula_str => $sat in wccs);
    };
}

macro_rules! wctl_bench_suite {
    ($($name:ident: $process_name:expr, $formula_str:expr => $sat:literal in $wccs:expr;)*) => {
        $(
        fn $name(c: &mut Criterion) {
            wctl_bench_suite_problem!($name: using c, $process_name, $formula_str => $sat in $wccs);
        }
        )*
        criterion_group!(
            name = benches;
            config = Criterion::default(); //.sample_size(20);
            targets = $($name),*
        );
    };
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
