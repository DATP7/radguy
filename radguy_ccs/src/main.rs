use radguy::{
    Arguments, Bottom, Cartesian, CopiedIter, Extract, Intersect, IsSubset, PairUniverse, Set,
    SliceRight, System, Union, Universe, Visited, kleene_local,
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
        strategy::{BinaryHeapStrategy, StrategyWeight},
    },
};

use crate::ordered::strategy::LazyHeap;
use radguy_ccs::systems::bool::strategic_extension::StrategicBoolExtension;

use radguy_ccs::systems::{
    bool::extension::BoolExtension,
    ccs::{
        bisimulation_system::BisimulationSystem, grammar::ProgramParser,
        transition_system::TransitionSystem, weak_transition_system::WeakTransitionSystem,
    },
    wccs::{self, wccs_system::WCCSSystem},
    wctl::{self, wctl_system::WCTLSystem},
};
use rayon::prelude::*;
use std::{
    collections::HashSet,
    fmt::{Debug, Display},
    fs::{self, File, OpenOptions},
    hash::Hash,
    io::{BufRead, BufReader, Write},
    path::{Path, PathBuf},
    sync::atomic::AtomicU32,
};

//TODO: Figure out how many iterations is a good amount
const ITERATIONS: u32 = 30;

fn append_record(file_path: &Path, record: &str) {
    let mut file = OpenOptions::new()
        .append(true)
        .create(true)
        .open(file_path)
        .expect("File should be created before this function call");

    if let Err(e) = writeln!(file, "{record}") {
        panic!("Couldn't write to file: {e}");
    }
}

fn record_exists(path: &Path, problem: &str, system: &str, oracle: &str) -> bool {
    let file = BufReader::new(File::open(path).expect("could not open file"));
    let pattern = format!("{problem},{system},{oracle}");
    file.lines()
        .any(|line| line.expect("could not read line").starts_with(&pattern))
}

fn create_csv() -> std::io::Result<PathBuf> {
    let path = PathBuf::from("./iteration_results/");
    if !path.exists() {
        fs::create_dir(&path)?;
    }

    let mut file_number = 0;
    let new_file_path;
    loop {
        let mut candidate_file = path.clone();
        candidate_file.push(format!("iterations_{file_number}.csv"));
        if !candidate_file.exists() {
            new_file_path = candidate_file;
            break;
        }
        file_number += 1;
    }

    let mut file = File::create(&new_file_path)?;
    writeln!(
        file,
        "Problem,System,Oracle,Ordered,VariableIterations,OracleIterations"
    )?;
    Ok(new_file_path)
}

macro_rules! weak_bisim_system_ordered_composed_unordered {
    ($file_path:expr, $name:ident, $left:expr, $right:expr => $ccs:expr, [$($strategic_oracle:expr),*]) => {
        $(
            weak_bisim_system_ordered! {
                $file_path, $name, $left, $right => $ccs,
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
    ($file_path:expr, $name:ident, $left:expr, $right:expr => $ccs:expr, [$($strategic_oracle:expr),*]) => {
        $(
            weak_bisim_system_ordered! {
                $file_path, $name, $left, $right => $ccs,
                BoolExtension::bitset().as_oracle().constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                SMax::bitset().then(BoolExtension::bitset().as_oracle()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
                LocalMaxR::bitset().then(BoolExtension::bitset().as_oracle()).constant(StrategyWeight::Num(1)).then($strategic_oracle.clone()),
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

macro_rules! weak_bisim_oracles {
    ($file_path:expr, $($name:ident: $left:expr, $right:expr => $ccs:expr;)*) => {
        $({
        weak_bisim_system! {
            $file_path, $name, $left, $right => $ccs,
            IdentityOracle::bitset(),
            TrivialOracle::bitset(),
            BoolExtension::bitset().as_oracle(),
            SMax::bitset().then(BoolExtension::bitset().as_oracle()),
            LocalMaxR::bitset().then(BoolExtension::bitset().as_oracle()),
            ArgumentsOracle::bitset().and(SMax::bitset()),
            ArgumentsOracle::bitset().and(LocalMaxR::bitset()),
            SMax::bitset(),
            LocalMaxR::bitset(),
            ArgumentsOracle::bitset(),
            ArgumentsOracle::bitset().then(SMax::bitset()),
            ArgumentsOracle::bitset().then(LocalMaxR::bitset()),
        }
        weak_bisim_system_ordered! {
            $file_path, $name, $left, $right => $ccs,
            IdentityOracle::bitset().ordered(),
            TrivialOracle::bitset().ordered(),

            SMax::bitset().ordered(),
            SMax::bitset().constant(StrategyWeight::Infinity),
            StrategicArgumentsOracle::default(),
            StrategicArgumentsOracle::default().and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min),
            StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()),
            StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default().then(BoolExtension::bitset().as_oracle().ordered()),
            StrategicArgumentsOracle::default().then(BoolExtension::bitset().as_oracle().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min),
            ArgumentsOracle::bitset().ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::bitset().ordered().then(InverseDependencyCountOracle::default()),
            DependencyCountOracle::default().and_by(BoolExtension::bitset().as_oracle().ordered(), std::cmp::min),
            InverseDependencyCountOracle::default().and_by(BoolExtension::bitset().as_oracle().ordered(), std::cmp::min),
            StrategicArgumentsOracle::default().then(StrategicBoolExtension::bitset().as_oracle()),
        }

        weak_bisim_system_ordered_composed_unordered!(
            $file_path, $name, $left, $right => $ccs,
            [
                DependencyCountOracle::default(),
                InverseDependencyCountOracle::default(),
                StrategicNonStuckOracle::bitset(),
                StrategicArgumentsOracle::default().then(StrategicBoolExtension::bitset().as_oracle()),
                DependencyCountOracle::default().then(StrategicBoolExtension::bitset().as_oracle())
            ]
        );
        })*
    };
}

macro_rules! weak_bisim_system {
    ($file_path:expr, $name:ident, $left:expr, $right:expr => $ccs:expr, $($oracle:expr,)*) => {
        let mut sys = generate_weak_ccs_system($ccs);
        let target = sys.specify_comparison($left, $right);

        $({
            run_unordered_kleene($file_path, "weak_bisimulation",stringify!($name), &sys, target, &$oracle)
        })*
    };
}

macro_rules! weak_bisim_system_ordered {
    ($file_path:expr, $name:ident, $left:expr, $right:expr => $ccs:expr, $($oracle:expr,)*) => {
        let mut sys = generate_weak_ccs_system($ccs);
        let target = sys.specify_comparison($left, $right);

        $({
            run_ordered_kleene($file_path, "weak_bisimulation",stringify!($name), &sys, target, &$oracle)
        })*
    };
}

fn generate_weak_ccs_system(
    ccs: &str,
) -> BisimulationSystem<usize, usize, usize, WeakTransitionSystem<usize>> {
    let parser = ProgramParser::new();
    let program_ast = parser
        .parse(ccs)
        .expect("Failed to parse CCS program content.");
    let mut weak_transition_system = WeakTransitionSystem::<usize>::default();
    weak_transition_system.load_ast(program_ast);

    BisimulationSystem::<usize, usize, usize, WeakTransitionSystem<usize>>::new(
        weak_transition_system,
    )
}

macro_rules! wctl_system_ordered_composed_unordered {
    ($file_path:expr, $name:ident: $proc:expr, $formula:expr => $wccs:expr, [$($strategic_oracle:expr),*]) => {
        $(
            wctl_system_ordered! {
                $file_path, $name: $proc, $formula => $wccs,
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
    ($file_path:expr, $name:ident: $proc:expr, $formula:expr => $wccs:expr, [$($strategic_oracle:expr),*]) => {
        $(
            wctl_system_ordered! {
                $file_path, $name: $proc, $formula => $wccs,
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

macro_rules! wctl_oracles {
    ($file_path:expr, $($name:ident: $proc:expr, $formula:expr => $wccs:expr;)*) => {
        $({
        wctl_system! {
            $file_path, $name: $proc, $formula => $wccs,
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
        wctl_system_ordered! {
            $file_path, $name: $proc, $formula => $wccs,
            IdentityOracle::bitset().ordered(),
            TrivialOracle::bitset().ordered(),

            SMax::bitset().ordered(),
            SMax::bitset().ordered().and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            SMax::bitset().constant(StrategyWeight::Infinity),
            SMax::bitset().constant(StrategyWeight::Infinity).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default(),
            StrategicArgumentsOracle::default().and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min),
            StrategicArgumentsOracle::default().and_by(SMax::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()),
            StrategicArgumentsOracle::default().then(LocalMaxR::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default().then(WeightedDepOracle::bitset().ordered()),
            StrategicArgumentsOracle::default().then(WeightedDepOracle::bitset().ordered()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::bitset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            ArgumentsOracle::bitset().ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::bitset().ordered().then(DependencyCountOracle::default()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            ArgumentsOracle::bitset().ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::bitset().ordered().then(InverseDependencyCountOracle::default()).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            DependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min),
            DependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
            InverseDependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min),
            InverseDependencyCountOracle::default().and_by(WeightedDepOracle::bitset().ordered(), std::cmp::min).and_by_with_name(StrategicNonStuckOracle::bitset(), std::cmp::min, "min"),
        }

        wctl_system_ordered_composed_unordered!(
            $file_path, $name: $proc, $formula => $wccs,
            [
                DependencyCountOracle::default(),
                InverseDependencyCountOracle::default(),
                StrategicNonStuckOracle::bitset()
            ]
        );
        })*
    };
}

macro_rules! wctl_system {
    ($file_path:expr, $name:ident: $process_name:expr, $formula:expr => $wccs:expr, $($oracle:expr,)*) => {
        let sys = generate_wctl_system($wccs);

        let formula_parser = wctl::grammar::FormulaParser::new();
        let formula = formula_parser.parse($formula).expect("Formula should parse");

        let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
        let formula_key = sys.insert_ast_formula(formula.clone());
        let target = sys.get_var(process_key, formula_key);

        $({
            run_unordered_kleene($file_path, "wctl",stringify!($name), &sys, target, &$oracle)
        })*
    };
}

macro_rules! wctl_system_ordered {
    ($file_path:expr, $name:ident: $process_name:expr, $formula:expr => $wccs:expr, $($oracle:expr,)*) => {
        let sys = generate_wctl_system($wccs);

        let formula_parser = wctl::grammar::FormulaParser::new();
        let formula = formula_parser.parse($formula).expect("Formula should parse");

        let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
        let formula_key = sys.insert_ast_formula(formula.clone());
        let target = sys.get_var(process_key, formula_key);

        $({
            run_ordered_kleene($file_path, "wctl",stringify!($name), &sys, target, &$oracle)
        })*
    };
}

fn generate_wctl_system(wccs: &str) -> WCTLSystem<usize, usize, usize, usize, usize> {
    let wccs_parser = wccs::ProgramParser::new();
    let wccs_ast = wccs_parser
        .parse(wccs)
        .expect("Failed to parse WCCS program content.");
    let mut wccs_system = WCCSSystem::<usize>::default();
    wccs_system.insert_ast_bindings(wccs_ast);

    WCTLSystem::<usize, usize, usize, usize, usize>::new(wccs_system)
}

fn run_unordered_kleene<
    K: Copy + Hash + Eq + Debug + Sync,
    V: Eq + PartialOrd + Bottom + Clone + Debug,
    VS: Set<K>
        + Intersect
        + Extract<K>
        + Default
        + Debug
        + Cartesian<HashSet<K>, Output = PS>
        + Cartesian<Output = PS>
        + Union<HashSet<K>>
        + for<'a> CopiedIter<'a, K>,
    PS: Set<(K, K)> + Union + SliceRight<K, K, VS> + Union<HashSet<(K, K)>> + Debug,
    S: System<K, V>
        + PairUniverse<PS>
        + Arguments<K, HashSet<K>>
        + Universe<VS>
        + Visited<VS>
        + Clone
        + Send,
    O: LocalOracle<K, V, PS, S> + Display + Clone + Send,
>(
    file_path: &Path,
    problem: &str,
    name: &str,
    system: &S,
    target: K,
    oracle: &O,
) where
    HashSet<K>: Cartesian<Output = HashSet<(K, K)>> + Cartesian<VS, Output = PS> + IsSubset<VS>,
{
    if record_exists(
        Path::new("skipped.txt"),
        problem,
        name,
        &format!("{oracle}"),
    ) || record_exists(file_path, problem, name, &format!("{oracle}"))
    {
        println!("skipping {problem}, {name}, {oracle}");
        return;
    }
    println!(
        "starting ({problem},{name},{oracle},false) at {}",
        chrono::Local::now()
    );
    let counter = AtomicU32::new(1);

    let pairs = (1..=ITERATIONS)
        .map(|_| ((*oracle).clone(), (*system).clone()))
        .collect::<Vec<_>>();
    let iterations: Vec<_> = pairs
        .into_par_iter()
        .filter_map(|(oracle, mut system)| {
            let Some((_, iteration)) = kleene_local(&mut system, target, &oracle) else {
                let c = counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                println!("{c}/{ITERATIONS} timed out at {}", chrono::Local::now());
                append_record(
                    Path::new("skipped.txt"),
                    &format!("{problem},{name},{oracle},false"),
                );
                return None;
            };

            let c = counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            println!("{c}/{ITERATIONS} finished at {}", chrono::Local::now());

            Some(iteration)
        })
        .collect();

    for (variable_iterations, oracle_iterations) in iterations {
        let record =
            format!("{problem},{name},{oracle},false,{variable_iterations},{oracle_iterations}");
        append_record(file_path, &record);
    }
}

fn run_ordered_kleene<
    VarKey: Copy + Eq + Debug + Hash + Default + Sync,
    VarValue: PartialOrd + Bottom + Copy + Debug,
    S: System<VarKey, VarValue>
        + Arguments<VarKey, HashSet<VarKey>>
        + Universe<HashSet<VarKey>>
        + PairUniverse<HashSet<(VarKey, VarKey)>>
        + Clone
        + Send,
    O: StrategicLocalOracle<
            VarKey,
            VarValue,
            LazyHeap<(VarKey, VarKey), BinaryHeapStrategy<(VarKey, VarKey)>>,
            S,
        > + Display
        + Clone
        + Send,
>(
    file_path: &Path,
    problem: &str,
    name: &str,
    system: &S,
    target: VarKey,
    oracle: &O,
) {
    if record_exists(
        Path::new("skipped.txt"),
        problem,
        name,
        &format!("{oracle}"),
    ) || record_exists(file_path, problem, name, &format!("{oracle}"))
    {
        println!("skipping {problem}, {name}, {oracle}");
        return;
    }
    println!(
        "starting ({problem},{name},{oracle},false) at {}",
        chrono::Local::now()
    );
    let counter = AtomicU32::new(1);

    let pairs = (1..=ITERATIONS)
        .map(|_| ((*oracle).clone(), (*system).clone()))
        .collect::<Vec<_>>();
    let iterations: Vec<_> = pairs
        .into_par_iter()
        .filter_map(|(oracle, mut system)| {
            let Some((_, iteration)) = ordered::kleene_local::<
                _,
                _,
                LazyHeap<_, BinaryHeapStrategy<_>>,
                LazyHeap<_, BinaryHeapStrategy<_>>,
                _,
            >(&mut system, target, &oracle) else {
                let c = counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                println!("{c}/{ITERATIONS} timed out at {}", chrono::Local::now());
                append_record(
                    &Path::new("skipped.txt"),
                    &format!("{problem},{name},{oracle},true"),
                );
                return None;
            };

            let c = counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            println!("{c}/{ITERATIONS} finished at {}", chrono::Local::now());

            Some(iteration)
        })
        .collect();

    for (variable_iterations, oracle_iterations) in iterations {
        let record =
            format!("{problem},{name},{oracle},true,{variable_iterations},{oracle_iterations}");
        append_record(file_path, &record);
    }
}

fn main() {
    let file_path = std::env::args().nth(1).map_or_else(
        || {
            let path = create_csv().expect("could not create output");
            println!(
                "no iterations file giving, writing to new file {}",
                path.display()
            );
            path
        },
        PathBuf::from,
    );

    weak_bisim_oracles! {
        &file_path,
        abp_ok: "SPEC", "ABP" => include_str!("../systems/ccs/abp_ok.ccs");
        abpl_ok: "SPEC", "ABPl" => include_str!("../systems/ccs/abp_ok.ccs");
        abpl_ok_2: "SPEC", "ABPl_2" => include_str!("../systems/ccs/abp_ok.ccs");
        abpl_bad_2: "SPEC", "ABPl_2" => include_str!("../systems/ccs/abp_bad.ccs");
        leader_election_ok_6: "Spec", "Ring" => include_str!("../systems/ccs/leader_election_ok_6.ccs");
        leader_election_bad_6: "Spec", "Ring" => include_str!("../systems/ccs/leader_election_bad_6.ccs");
        leader_election_bad_7: "Spec", "Ring" => include_str!("../systems/ccs/leader_election_bad_7.ccs");
        leader_election_ok_7: "Spec", "Ring" => include_str!("../systems/ccs/leader_election_ok_7.ccs");
        leader_election_bad_8: "Spec", "Ring" => include_str!("../systems/ccs/leader_election_bad_8.ccs");
        leader_election_ok_8: "Spec", "Ring" => include_str!("../systems/ccs/leader_election_ok_8.ccs");
        dekker_mutual_exclusion: "Dekker-2", "Spec" => include_str!("../systems/ccs/dekkers_mutual_exclusion.ccs");

        // NOTE: these two actually *are* weakly bisimilar, so should not be used
        // abp_bad: "SPEC", "ABP" => include_str!("../systems/ccs/abp_bad.ccs");
        // abpl_bad: "SPEC", "ABPl" => include_str!("../systems/ccs/abp_bad.ccs");
    }

    wctl_oracles! {
        &file_path,
        leader_election_6: "Ring", "EF leader" => include_str!("../systems/wccs/LeaderElection6.wccs");
        leader_election_neg_6: "Ring", "EF leader > 1" => include_str!("../systems/wccs/LeaderElection6.wccs");
        leader_election_7: "Ring", "EF leader" => include_str!("../systems/wccs/LeaderElection7.wccs");
        leader_election_neg_7: "Ring", "EF leader > 1" => include_str!("../systems/wccs/LeaderElection7.wccs");
        leader_election_8: "Ring", "EF leader" => include_str!("../systems/wccs/LeaderElection8.wccs");
        leader_election_neg_8: "Ring", "EF leader > 1" => include_str!("../systems/wccs/LeaderElection8.wccs");
        semaphore_3_5_fail: "System", "EF critical_section > 3" => include_str!("../systems/wccs/Semaphore_3_5.wccs");
        semaphore_3_5_succ: "System", "EF critical_section == 3" => include_str!("../systems/wccs/Semaphore_3_5.wccs");
        semaphore_4_5_fail: "System", "EF critical_section > 4" => include_str!("../systems/wccs/Semaphore_4_5.wccs");
        semaphore_4_5_succ: "System", "EF critical_section == 4" => include_str!("../systems/wccs/Semaphore_4_5.wccs");
        client_server_failed_5: "System", "E True U[<=5] failed" => include_str!("../systems/wccs/ClientServer.wccs");
        client_server_deliver_7: "System", "E True U[<=8] delivered" => include_str!("../systems/wccs/ClientServer.wccs");
        client_server_big: "System", "E True U[<=10] (A True U[<=1] failed)" => include_str!("../systems/wccs/ClientServer.wccs");
    }
}
