use radguy::{
    Arguments, Bottom, Cartesian, CopiedIter, Intersect, IsSubset, PairUniverse, Set, SliceRight,
    System, Union, Universe, Visited, kleene_local,
    oracle::{
        ArgumentsOracle, IdentityOracle, LocalMaxR, LocalOracle, SMax, TrivialOracle,
        WeightedDepOracle,
    },
    ordered::{
        self,
        oracle::{
            DependencyCountOracle, InverseDependencyCountOracle, SiblingsOracle, SiblingsOracleInv,
            StrategicArgumentsOracle, StrategicLocalOracle, ToConstant, ToOrdered,
        },
        strategy::{BinaryHeapStrategy, StrategyWeight},
    },
};
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

macro_rules! weak_bisim_oracles {
    ($file_path:expr, $($name:ident: $left:expr, $right:expr => $ccs:expr;)*) => {
        $({
        weak_bisim_system! {
            $file_path, $name, $left, $right => $ccs,
            IdentityOracle::hashset(),
            TrivialOracle::hashset(),
            BoolExtension::hashset().as_oracle(),
            SMax::hashset().then(BoolExtension::hashset().as_oracle()),
            LocalMaxR::hashset().then(BoolExtension::hashset().as_oracle()),
            ArgumentsOracle::hashset().and(SMax::hashset()),
            ArgumentsOracle::hashset().and(LocalMaxR::hashset()),
            SMax::hashset(),
            LocalMaxR::hashset(),
            ArgumentsOracle::hashset(),
            ArgumentsOracle::hashset().then(SMax::hashset()),
            ArgumentsOracle::hashset().then(LocalMaxR::hashset()),
        }
        weak_bisim_system_ordered! {
            $file_path, $name, $left, $right => $ccs,
            IdentityOracle::hashset().ordered(),
            TrivialOracle::hashset().ordered(),

            BoolExtension::hashset().as_oracle().ordered().then(SiblingsOracleInv),
            SMax::hashset().then(BoolExtension::hashset().as_oracle()).ordered().then(SiblingsOracleInv),
            LocalMaxR::hashset().then(BoolExtension::hashset().as_oracle()).ordered().then(SiblingsOracleInv),
            ArgumentsOracle::hashset().and(SMax::hashset()).ordered().then(SiblingsOracleInv),
            ArgumentsOracle::hashset().and(LocalMaxR::hashset()).ordered().then(SiblingsOracleInv),
            SMax::hashset().ordered().then(SiblingsOracleInv),
            LocalMaxR::hashset().ordered().then(SiblingsOracleInv),
            ArgumentsOracle::hashset().ordered().then(SiblingsOracleInv),
            ArgumentsOracle::hashset().then(SMax::hashset()).ordered().then(SiblingsOracleInv),
            ArgumentsOracle::hashset().then(LocalMaxR::hashset()).ordered().then(SiblingsOracleInv),

            BoolExtension::hashset().as_oracle().ordered().then(DependencyCountOracle::default()),
            SMax::hashset().then(BoolExtension::hashset().as_oracle()).ordered().then(DependencyCountOracle::default()),
            LocalMaxR::hashset().then(BoolExtension::hashset().as_oracle()).ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().and(SMax::hashset()).ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().and(LocalMaxR::hashset()).ordered().then(DependencyCountOracle::default()),
            SMax::hashset().ordered().then(DependencyCountOracle::default()),
            LocalMaxR::hashset().ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().then(SMax::hashset()).ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().then(LocalMaxR::hashset()).ordered().then(DependencyCountOracle::default()),

            BoolExtension::hashset().as_oracle().ordered().then(InverseDependencyCountOracle::default()),
            SMax::hashset().then(BoolExtension::hashset().as_oracle()).ordered().then(InverseDependencyCountOracle::default()),
            LocalMaxR::hashset().then(BoolExtension::hashset().as_oracle()).ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::hashset().and(SMax::hashset()).ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::hashset().and(LocalMaxR::hashset()).ordered().then(InverseDependencyCountOracle::default()),
            SMax::hashset().ordered().then(InverseDependencyCountOracle::default()),
            LocalMaxR::hashset().ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::hashset().ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::hashset().then(SMax::hashset()).ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::hashset().then(LocalMaxR::hashset()).ordered().then(InverseDependencyCountOracle::default()),

            BoolExtension::hashset().as_oracle().ordered().then(SiblingsOracle),
            SMax::hashset().then(BoolExtension::hashset().as_oracle()).ordered().then(SiblingsOracle),
            LocalMaxR::hashset().then(BoolExtension::hashset().as_oracle()).ordered().then(SiblingsOracle),
            ArgumentsOracle::hashset().and(SMax::hashset()).ordered().then(SiblingsOracle),
            ArgumentsOracle::hashset().and(LocalMaxR::hashset()).ordered().then(SiblingsOracle),
            SMax::hashset().ordered().then(SiblingsOracle),
            LocalMaxR::hashset().ordered().then(SiblingsOracle),
            ArgumentsOracle::hashset().ordered().then(SiblingsOracle),
            ArgumentsOracle::hashset().then(SMax::hashset()).ordered().then(SiblingsOracle),
            ArgumentsOracle::hashset().then(LocalMaxR::hashset()).ordered().then(SiblingsOracle),

            StrategicArgumentsOracle::default(),
            SMax::hashset().ordered(),
            SMax::hashset().constant(StrategyWeight::Infinity),
            StrategicArgumentsOracle::default().and_by(SMax::hashset().ordered(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::hashset().ordered()),
            StrategicArgumentsOracle::default().then(LocalMaxR::hashset().ordered()),
            StrategicArgumentsOracle::default().then(BoolExtension::hashset().as_oracle().ordered()),
            StrategicArgumentsOracle::default().then(SMax::hashset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::hashset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min),
            ArgumentsOracle::hashset().ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().ordered().then(InverseDependencyCountOracle::default()),
            DependencyCountOracle::default().and_by(BoolExtension::hashset().as_oracle().ordered(), std::cmp::min),
            InverseDependencyCountOracle::default().and_by(BoolExtension::hashset().as_oracle().ordered(), std::cmp::min),
        }
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

macro_rules! wctl_oracles {
    ($file_path:expr, $($name:ident: $proc:expr, $formula:expr => $wccs:expr;)*) => {
        $({
        wctl_system! {
            $file_path, $name: $proc, $formula => $wccs,
            IdentityOracle::hashset(),
            TrivialOracle::hashset(),
            WeightedDepOracle::hashset(),
            SMax::hashset().then(WeightedDepOracle::hashset()),
            LocalMaxR::hashset().then(WeightedDepOracle::hashset()),
            ArgumentsOracle::hashset().and(SMax::hashset()),
            ArgumentsOracle::hashset().and(LocalMaxR::hashset()),
            SMax::hashset(),
            LocalMaxR::hashset(),
            ArgumentsOracle::hashset(),
            ArgumentsOracle::hashset().then(SMax::hashset()),
            ArgumentsOracle::hashset().then(LocalMaxR::hashset()),
        }
        wctl_system_ordered! {
            $file_path, $name: $proc, $formula => $wccs,
            IdentityOracle::hashset().ordered(),
            TrivialOracle::hashset().ordered(),

            WeightedDepOracle::hashset().ordered().then(SiblingsOracleInv),
            SMax::hashset().then(WeightedDepOracle::hashset()).ordered().then(SiblingsOracleInv),
            LocalMaxR::hashset().then(WeightedDepOracle::hashset()).ordered().then(SiblingsOracleInv),
            ArgumentsOracle::hashset().and(SMax::hashset()).ordered().then(SiblingsOracleInv),
            ArgumentsOracle::hashset().and(LocalMaxR::hashset()).ordered().then(SiblingsOracleInv),
            SMax::hashset().ordered().then(SiblingsOracleInv),
            LocalMaxR::hashset().ordered().then(SiblingsOracleInv),
            ArgumentsOracle::hashset().ordered().then(SiblingsOracleInv),
            ArgumentsOracle::hashset().then(SMax::hashset()).ordered().then(SiblingsOracleInv),
            ArgumentsOracle::hashset().then(LocalMaxR::hashset()).ordered().then(SiblingsOracleInv),

            WeightedDepOracle::hashset().ordered().then(DependencyCountOracle::default()),
            SMax::hashset().then(WeightedDepOracle::hashset()).ordered().then(DependencyCountOracle::default()),
            LocalMaxR::hashset().then(WeightedDepOracle::hashset()).ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().and(SMax::hashset()).ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().and(LocalMaxR::hashset()).ordered().then(DependencyCountOracle::default()),
            SMax::hashset().ordered().then(DependencyCountOracle::default()),
            LocalMaxR::hashset().ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().then(SMax::hashset()).ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().then(LocalMaxR::hashset()).ordered().then(DependencyCountOracle::default()),

            WeightedDepOracle::hashset().ordered().then(InverseDependencyCountOracle::default()),
            SMax::hashset().then(WeightedDepOracle::hashset()).ordered().then(InverseDependencyCountOracle::default()),
            LocalMaxR::hashset().then(WeightedDepOracle::hashset()).ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::hashset().and(SMax::hashset()).ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::hashset().and(LocalMaxR::hashset()).ordered().then(InverseDependencyCountOracle::default()),
            SMax::hashset().ordered().then(InverseDependencyCountOracle::default()),
            LocalMaxR::hashset().ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::hashset().ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::hashset().then(SMax::hashset()).ordered().then(InverseDependencyCountOracle::default()),
            ArgumentsOracle::hashset().then(LocalMaxR::hashset()).ordered().then(InverseDependencyCountOracle::default()),

            WeightedDepOracle::hashset().ordered().then(SiblingsOracle),
            SMax::hashset().then(WeightedDepOracle::hashset()).ordered().then(SiblingsOracle),
            LocalMaxR::hashset().then(WeightedDepOracle::hashset()).ordered().then(SiblingsOracle),
            ArgumentsOracle::hashset().and(SMax::hashset()).ordered().then(SiblingsOracle),
            ArgumentsOracle::hashset().and(LocalMaxR::hashset()).ordered().then(SiblingsOracle),
            SMax::hashset().ordered().then(SiblingsOracle),
            LocalMaxR::hashset().ordered().then(SiblingsOracle),
            ArgumentsOracle::hashset().ordered().then(SiblingsOracle),
            ArgumentsOracle::hashset().then(SMax::hashset()).ordered().then(SiblingsOracle),
            ArgumentsOracle::hashset().then(LocalMaxR::hashset()).ordered().then(SiblingsOracle),

            StrategicArgumentsOracle::default(),
            SMax::hashset().ordered(),
            SMax::hashset().constant(StrategyWeight::Infinity),
            StrategicArgumentsOracle::default().and_by(SMax::hashset().ordered(), std::cmp::min),
            StrategicArgumentsOracle::default().and_by(SMax::hashset().ordered(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::hashset().ordered()),
            StrategicArgumentsOracle::default().then(LocalMaxR::hashset().ordered()),
            StrategicArgumentsOracle::default().then(WeightedDepOracle::hashset().ordered()),
            StrategicArgumentsOracle::default().then(SMax::hashset().ordered()).and_by(DependencyCountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default().then(SMax::hashset().ordered()).and_by(InverseDependencyCountOracle::default(), std::cmp::min),
            ArgumentsOracle::hashset().ordered().then(DependencyCountOracle::default()),
            ArgumentsOracle::hashset().ordered().then(InverseDependencyCountOracle::default()),
            DependencyCountOracle::default().and_by(WeightedDepOracle::hashset().ordered(), std::cmp::min),
            InverseDependencyCountOracle::default().and_by(WeightedDepOracle::hashset().ordered(), std::cmp::min),
        }
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
    V: Eq + PartialOrd + Bottom + Clone,
    VS: Set<K>
        + Intersect
        + Default
        + Cartesian<HashSet<K>, Output = PS>
        + Cartesian<Output = PS>
        + Union<HashSet<K>>
        + for<'a> CopiedIter<'a, K>,
    PS: Set<(K, K)> + Union + SliceRight<K, K, VS> + Union<HashSet<(K, K)>>,
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
    if record_exists(file_path, problem, name, &format!("{oracle}")) {
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
        .map(|(oracle, mut system)| {
            let (_, iteration) = kleene_local(&mut system, target, &oracle);

            let c = counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            println!("{c}/{ITERATIONS} finished at {}", chrono::Local::now());

            iteration
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
    O: StrategicLocalOracle<VarKey, VarValue, BinaryHeapStrategy<(VarKey, VarKey)>, S>
        + Display
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
    if record_exists(file_path, problem, name, &format!("{oracle}")) {
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
        .map(|(oracle, mut system)| {
            let (_, iteration) =
                ordered::kleene_local::<_, _, BinaryHeapStrategy<_>, BinaryHeapStrategy<_>, _>(
                    &mut system,
                    target,
                    &oracle,
                );

            let c = counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            println!("{c}/{ITERATIONS} finished at {}", chrono::Local::now());

            iteration
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
        dekker_mutual_exclusion: "Dekker-2", "Spec" => include_str!("../systems/ccs/dekkers_mutual_exclusion.ccs");

        // NOTE: these two actually *are* weakly bisimilar, so should not be used
        // abp_bad: "SPEC", "ABP" => include_str!("../systems/ccs/abp_bad.ccs");
        // abpl_bad: "SPEC", "ABPl" => include_str!("../systems/ccs/abp_bad.ccs");
    }

    wctl_oracles! {
        &file_path,
        mower_example:
            "S0", "A mow U[<=6] dump" =>r"
        S0 := mow:(<go,2>.S1 + <go,2>.S2 + <go,2>.S3);
        S1 := mow:<go,1>.S4;
        S2 := mow:<go,2>.S4;
        S3 := mow:<go,1>.S5;
        S4 := mow:(<go,0>.S5 + <go,1>.S6);
        S5 := mow:<go,2>.S6;
        S6 := dump:<go,0>.S6;
    ";
        mower_example_neg: "S0", "A mow U[<=4] dump" => r"
        S0 := mow:(<go,2>.S1 + <go,2>.S2 + <go,2>.S3);
        S1 := mow:<go,1>.S4;
        S2 := mow:<go,2>.S4;
        S3 := mow:<go,1>.S5;
        S4 := mow:(<go,0>.S5 + <go,1>.S6);
        S5 := mow:<go,2>.S6;
        S6 := dump:<go,0>.S6;
    ";
        proposition: "S", "mow" => "S := mow:0;";
        proposition_multiple: "S", "mow && dump" => "S := mow:dump:0;";
        proposition_multiple_neg: "S", "mow && dump && dud" => "S := mow:dump:0;";
        linear_universal_final: "S", "AF dump" => "S := <go>.<go>.<go>.<go>.dump:0;";
        recursive: "S", "AF dump" => "S := <go>.dump:S;";
        recursive_neg: "S", "AF mow" => "S := <go>.dump:S;";
        compare: "S", "mow == 4" => "S := mow:0 + mow:0 + mow:0 + mow:0;";
        leader_election_2: "Ring", "EF leader" => include_str!("../systems/wccs/LeaderElection2.wccs");
        leader_election_6: "Ring", "EF leader" => include_str!("../systems/wccs/LeaderElection6.wccs");
        leader_election_neg_2: "Ring", "EF leader > 1" => include_str!("../systems/wccs/LeaderElection2.wccs");
        leader_election_neg_6: "Ring", "EF leader > 1" => include_str!("../systems/wccs/LeaderElection6.wccs");
    }
}
