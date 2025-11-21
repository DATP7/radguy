use radguy::{
    Arguments, Bottom, Cartesian, CopiedIter, Intersect, IsSubset, PairUniverse, Set, SliceRight,
    System, Union, Universe, Visited, kleene_local,
    oracle::{ArgumentsOracle, LocalMaxR, LocalOracle, SMax, WeightedDepOracle},
    ordered::{
        self,
        oracle::{
            DependencyCountOracle, InverseDependencyCountOracle, SiblingsOracle,
            StrategicArgumentsOracle, StrategicHeightOracle, StrategicLocalOracle, ToConstant,
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
    io::Write,
    path::PathBuf,
};

//TODO: Figure out how many iterations is a good amount
const ITERATIONS: u32 = 10;

fn append_record(file_path: &PathBuf, record: &str) {
    let mut file = OpenOptions::new()
        .append(true)
        .open(file_path)
        .expect("File should be created before this function call");

    if let Err(e) = writeln!(file, "{record}") {
        panic!("Couldn't write to file: {e}");
    }
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
    writeln!(file, "Problem,System,Oracle,Ordered,Iters")?;
    Ok(new_file_path)
}

macro_rules! weak_bisim_oracles {
    ($file_path:expr, $($name:ident: $left:expr, $right:expr => $ccs:expr;)*) => {
        $({
        weak_bisim_system! {
            $file_path, $name, $left, $right => $ccs,
            SMax::bitset(),
            LocalMaxR::bitset(),
            ArgumentsOracle::bitset(),
            ArgumentsOracle::bitset().then(SMax::bitset()),
            ArgumentsOracle::bitset().then(LocalMaxR::bitset()),
            ArgumentsOracle::bitset().and(SMax::bitset()),
            ArgumentsOracle::bitset().and(LocalMaxR::bitset()),
            BoolExtension::bitset().as_oracle(),
            SMax::bitset().then(BoolExtension::bitset().as_oracle()),
            LocalMaxR::bitset().then(BoolExtension::bitset().as_oracle()),
        }
        weak_bisim_system_ordered! {
            $file_path, $name, $left, $right => $ccs,
            SMax::bitset().constant(StrategyWeight::Infinity),
            LocalMaxR::bitset().constant(StrategyWeight::Infinity),
            LocalMaxR::bitset().constant(StrategyWeight::Infinity).then(DependencyCountOracle::default()),
            LocalMaxR::bitset().constant(StrategyWeight::Infinity).then(InverseDependencyCountOracle::default()),
            BoolExtension::bitset().as_oracle().constant(StrategyWeight::Infinity).and_by(InverseDependencyCountOracle::default(), std::cmp::min),
            BoolExtension::bitset().as_oracle().constant(StrategyWeight::Infinity).and_by(DependencyCountOracle::default(), std::cmp::min),
            BoolExtension::bitset().as_oracle().constant(StrategyWeight::Num(1)).then(SiblingsOracle),
            StrategicArgumentsOracle::default(),
            StrategicArgumentsOracle::default().and_by(DependencyCountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default().and_by(InverseDependencyCountOracle::default(), std::cmp::min),
            DependencyCountOracle::default().then(StrategicArgumentsOracle::default()),
            InverseDependencyCountOracle::default().then(StrategicArgumentsOracle::default()),
            StrategicArgumentsOracle::default().then(DependencyCountOracle::default()),
            StrategicArgumentsOracle::default().then(InverseDependencyCountOracle::default()),
            StrategicArgumentsOracle::default().and_by(SMax::bitset().constant(StrategyWeight::Infinity), std::cmp::min).then(DependencyCountOracle::default()),
            StrategicArgumentsOracle::default().and_by(SMax::bitset().constant(StrategyWeight::Infinity), std::cmp::min).then(InverseDependencyCountOracle::default()),
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
            SMax::bitset(),
            LocalMaxR::bitset(),
            WeightedDepOracle::default(),
            ArgumentsOracle::bitset(),
            ArgumentsOracle::bitset().then(SMax::bitset()),
            ArgumentsOracle::bitset().then(LocalMaxR::bitset()),
            ArgumentsOracle::bitset().and(SMax::bitset()),
            ArgumentsOracle::bitset().and(LocalMaxR::bitset()),
        }
        wctl_system_ordered! {
            $file_path, $name: $proc, $formula => $wccs,
            SMax::bitset().constant(StrategyWeight::Infinity),
            LocalMaxR::bitset().constant(StrategyWeight::Infinity),
            LocalMaxR::bitset().constant(StrategyWeight::Infinity).then(DependencyCountOracle::default()),
            LocalMaxR::bitset().constant(StrategyWeight::Infinity).then(InverseDependencyCountOracle::default()),
            WeightedDepOracle::default().constant(StrategyWeight::Num(1)).then(SiblingsOracle),
            StrategicArgumentsOracle::default(),
            StrategicArgumentsOracle::default().and_by(DependencyCountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default().and_by(InverseDependencyCountOracle::default(), std::cmp::min),
            DependencyCountOracle::default().then(StrategicArgumentsOracle::default()),
            InverseDependencyCountOracle::default().then(StrategicArgumentsOracle::default()),
            StrategicArgumentsOracle::default().then(DependencyCountOracle::default()),
            StrategicArgumentsOracle::default().then(InverseDependencyCountOracle::default()),
            StrategicArgumentsOracle::default().and_by(SMax::bitset().constant(StrategyWeight::Infinity), std::cmp::min).then(DependencyCountOracle::default()),
            StrategicArgumentsOracle::default().and_by(SMax::bitset().constant(StrategyWeight::Infinity), std::cmp::min).then(InverseDependencyCountOracle::default()),
            StrategicArgumentsOracle::default().then(StrategicHeightOracle::simple()),
            StrategicArgumentsOracle::default().then(StrategicHeightOracle::transitive()),
            LocalMaxR::bitset().constant(StrategyWeight::Infinity).then(InverseDependencyCountOracle::default()).then(StrategicHeightOracle::simple()),
            LocalMaxR::bitset().constant(StrategyWeight::Infinity).then(InverseDependencyCountOracle::default()).then(StrategicHeightOracle::transitive()),
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
    file_path: &PathBuf,
    problem: &str,
    name: &str,
    system: &S,
    target: K,
    oracle: &O,
) where
    HashSet<K>: Cartesian<Output = HashSet<(K, K)>> + Cartesian<VS, Output = PS> + IsSubset<VS>,
{
    let pairs = (1..=ITERATIONS)
        .map(|_| ((*oracle).clone(), (*system).clone()))
        .collect::<Vec<_>>();
    let iterations: Vec<_> = pairs
        .into_par_iter()
        .map(|(oracle, mut system)| {
            let (_, iteration) = kleene_local(&mut system, target, &oracle);
            iteration
        })
        .collect();

    for i in iterations {
        let record = format!("{problem},{name},{oracle},false,{i}");
        append_record(file_path, &record);
    }
}

fn run_ordered_kleene<
    VarKey: Copy + Eq + Debug + Hash + Default + Sync,
    VarValue: PartialOrd + Bottom + Copy,
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
    file_path: &PathBuf,
    problem: &str,
    name: &str,
    system: &S,
    target: VarKey,
    oracle: &O,
) {
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
            iteration
        })
        .collect();

    for i in iterations {
        let record = format!("{problem},{name},{oracle},true,{i}");
        append_record(file_path, &record);
    }
}

fn main() {
    let file_path = match create_csv() {
        Ok(path) => path,
        Err(e) => panic!("{e}"),
    };

    weak_bisim_oracles! {
        &file_path,
        abp_ok: "SPEC", "ABP" => include_str!("../systems/ccs/abp_ok.ccs");
        abpl_ok: "SPEC", "ABPl" => include_str!("../systems/ccs/abp_ok.ccs");
        abpl_ok_2: "SPEC", "ABPl_2" => include_str!("../systems/ccs/abp_ok.ccs");
        abpl_bad_2: "SPEC", "ABPl_2" => include_str!("../systems/ccs/abp_bad.ccs");
        abpl_ok_3: "SPEC", "ABPl_3" => include_str!("../systems/ccs/abp_ok.ccs");
        abpl_bad_3: "SPEC", "ABPl_3" => include_str!("../systems/ccs/abp_bad.ccs");
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
        leader_election: "Ring", "EF leader" => include_str!("../systems/wccs/LeaderElection2.wccs");
        leader_election_neg: "Ring", "EF leader > 1" => include_str!("../systems/wccs/LeaderElection2.wccs");
    }
}
