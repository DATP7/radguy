use radguy::{
    Arguments, Bottom, Cartesian, PairUniverse, System, Union, Universe,
    extension::LocalExtension,
    kleene_local,
    oracle::{ArgumentsOracle, LocalMaxR, LocalOracle, SMax},
    ordered::{
        self,
        oracle::{
            CountOracle, InverseCountOracle, StrategicArgumentsOracle, StrategicHeightOracle,
            StrategicLocalOracle, ToConstant,
        },
        strategy::{BinaryHeapStrategy, StrategyWeight},
    },
};
use std::{
    collections::HashSet,
    fmt::{Debug, Display},
    fs::{self, File, OpenOptions},
    hash::Hash,
    io::Write,
    path::PathBuf,
};

use slotmap::DefaultKey;

use radguy_ccs::systems::{
    bool::extension::BoolExtension,
    ccs::{
        bisimulation_system::BisimulationSystem, grammar::ProgramParser,
        transition_system::TransitionSystem, weak_transition_system::WeakTransitionSystem,
    },
    wccs::{self, wccs_system::WCCSSystem},
    wctl::{self, wctl_system::WCTLSystem},
};

//TODO: Figure out how many iterations is a good amount
const ITERATIONS: u32 = 10;

fn append_record(record: &str) {
    let mut file = OpenOptions::new()
        .append(true)
        .open("./iteration_results/new_iterations.csv")
        .expect("File should be created before this function call");

    if let Err(e) = writeln!(file, "{record}") {
        panic!("Couldn't write to file: {e}");
    }
}

fn create_csv() -> std::io::Result<()> {
    let path = PathBuf::from("./iteration_results/");
    if !path.exists() {
        fs::create_dir(&path)?;
    }

    let mut new_file = path.clone();
    new_file.push("new_iterations.csv");
    if new_file.exists() {
        let mut old_file = path;
        old_file.push("pre_iterations.csv");
        fs::rename(&new_file, old_file)?;
    }
    let mut file = File::create(&new_file)?;
    writeln!(file, "Problem,System,Oracle,Ordered,Iters")
}

macro_rules! weak_bisim_oracles {
    ($($name:ident: $left:expr, $right:expr => $ccs:expr;)*) => {
        $({
        weak_bisim_system! {
            $name, $left, $right => $ccs,
            SMax::default(),
            // TODO: LocalMaxR and Arguments should be fixed
            LocalMaxR::default(),
            ArgumentsOracle::default(),
            ArgumentsOracle::default().then(SMax::default()),
            ArgumentsOracle::default().then(LocalMaxR::default()),
            ArgumentsOracle::default().and(SMax::default()),
            ArgumentsOracle::default().and(LocalMaxR::default()),
            BoolExtension::oracle(),
            SMax::default().then(BoolExtension::oracle()),
            LocalMaxR::default().then(BoolExtension::oracle()),
        }
        weak_bisim_system_ordered! {
            $name, $left, $right => $ccs,
            SMax::default().constant(StrategyWeight::Infinity),
            LocalMaxR::default().constant(StrategyWeight::Infinity),
            LocalMaxR::default().constant(StrategyWeight::Infinity).then(CountOracle::default()),
            LocalMaxR::default().constant(StrategyWeight::Infinity).then(InverseCountOracle::default()),
            BoolExtension::oracle().constant(StrategyWeight::Infinity).and_by(InverseCountOracle::default(), std::cmp::min),
            BoolExtension::oracle().constant(StrategyWeight::Infinity).and_by(CountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default(),
            StrategicArgumentsOracle::default().and_by(CountOracle::default(), std::cmp::min),
            StrategicArgumentsOracle::default().and_by(InverseCountOracle::default(), std::cmp::min),
            CountOracle::default().then(StrategicArgumentsOracle::default()),
            InverseCountOracle::default().then(StrategicArgumentsOracle::default()),
            StrategicArgumentsOracle::default().then(CountOracle::default()),
            StrategicArgumentsOracle::default().then(InverseCountOracle::default()),
            StrategicArgumentsOracle::default().and_by(SMax::default().constant(StrategyWeight::Infinity), std::cmp::min).then(CountOracle::default()),
            StrategicArgumentsOracle::default().and_by(SMax::default().constant(StrategyWeight::Infinity), std::cmp::min).then(InverseCountOracle::default()),
        }
        })*
    };
}

macro_rules! weak_bisim_system {
    ($name:ident, $left:expr, $right:expr => $ccs:expr, $($oracle:expr,)*) => {
        let mut sys = generate_weak_ccs_system($ccs);
        let target = sys.specify_comparison($left, $right);

        $({
            run_kleene("weak_bisimulation",stringify!($name), &sys, target, &$oracle)
        })*
    };
}

macro_rules! weak_bisim_system_ordered {
    ($name:ident, $left:expr, $right:expr => $ccs:expr, $($oracle:expr,)*) => {
        let mut sys = generate_weak_ccs_system($ccs);
        let target = sys.specify_comparison($left, $right);

        $({
            run_ordered_kleene("weak_bisimulation",stringify!($name), &sys, target, &$oracle)
        })*
    };
}

fn generate_weak_ccs_system(
    ccs: &str,
) -> BisimulationSystem<DefaultKey, DefaultKey, DefaultKey, WeakTransitionSystem<DefaultKey>> {
    let parser = ProgramParser::new();
    let program_ast = parser
        .parse(ccs)
        .expect("Failed to parse CCS program content.");
    let mut weak_transition_system = WeakTransitionSystem::<DefaultKey>::default();
    weak_transition_system.load_ast(program_ast);

    BisimulationSystem::<DefaultKey, DefaultKey, DefaultKey, WeakTransitionSystem<DefaultKey>>::new(
        weak_transition_system,
    )
}

macro_rules! wctl_oracles {
    ($($name:ident: $proc:expr, $formula:expr => $wccs:expr;)*) => {
        $({
        wctl_system! {
            $name: $proc, $formula => $wccs,
            SMax::default(),
            LocalMaxR::default(),
            ArgumentsOracle::default(),
            ArgumentsOracle::default().then(SMax::default()),
            ArgumentsOracle::default().then(LocalMaxR::default()),
            ArgumentsOracle::default().and(SMax::default()),
            ArgumentsOracle::default().and(LocalMaxR::default()),
        }
        wctl_system_ordered! {
            $name: $proc, $formula => $wccs,
            SMax::default().constant(StrategyWeight::Infinity),
            LocalMaxR::default().constant(StrategyWeight::Infinity),
            LocalMaxR::default().constant(StrategyWeight::Infinity).then(CountOracle::default()),
            LocalMaxR::default().constant(StrategyWeight::Infinity).then(InverseCountOracle::default()),
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
        }
        })*

    };
}

macro_rules! wctl_system {
    ($name:ident: $process_name:expr, $formula:expr => $wccs:expr, $($oracle:expr,)*) => {
        let sys = generate_wctl_system($wccs);

        let formula_parser = wctl::grammar::FormulaParser::new();
        let formula = formula_parser.parse($formula).expect("Formula should parse");

        let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
        let formula_key = sys.insert_ast_formula(formula.clone());
        let target = sys.get_var(process_key, formula_key);

        $({
            run_kleene("wctl",stringify!($name), &sys, target, &$oracle)
        })*
    };
}

macro_rules! wctl_system_ordered {
    ($name:ident: $process_name:expr, $formula:expr => $wccs:expr, $($oracle:expr,)*) => {
        let sys = generate_wctl_system($wccs);

        let formula_parser = wctl::grammar::FormulaParser::new();
        let formula = formula_parser.parse($formula).expect("Formula should parse");

        let process_key = sys.get_process_definition($process_name).expect("Process name should be bound");
        let formula_key = sys.insert_ast_formula(formula.clone());
        let target = sys.get_var(process_key, formula_key);

        $({
            run_ordered_kleene("wctl",stringify!($name), &sys, target, &$oracle)
        })*
    };
}

fn generate_wctl_system(
    wccs: &str,
) -> WCTLSystem<DefaultKey, DefaultKey, DefaultKey, DefaultKey, DefaultKey> {
    let wccs_parser = wccs::ProgramParser::new();
    let wccs_ast = wccs_parser
        .parse(wccs)
        .expect("Failed to parse WCCS program content.");
    let mut wccs_system = WCCSSystem::<DefaultKey>::default();
    wccs_system.insert_ast_bindings(wccs_ast);

    WCTLSystem::<DefaultKey, DefaultKey, DefaultKey, DefaultKey, DefaultKey>::new(wccs_system)
}

fn run_kleene<
    K: Copy + Hash + Eq + Debug,
    V: Eq + PartialOrd + Bottom + Clone,
    PS: Debug + Union,
    S: System<K, V> + PairUniverse<PS> + Arguments<K, HashSet<K>> + Universe<HashSet<K>> + Clone,
    O: LocalOracle<K, V, PS, S> + Display + Clone,
>(
    problem: &str,
    name: &str,
    system: &S,
    target: K,
    oracle: &O,
) where
    for<'a> &'a PS: IntoIterator<Item = &'a (K, K)>,
    HashSet<K>: Cartesian<Output = PS>,
{
    for _ in 1..=ITERATIONS {
        let oracle = (*oracle).clone();
        let mut system = (*system).clone();
        let (_, iterations) = kleene_local(&mut system, target, &oracle);
        let record = format!("{problem},{name},{oracle},false,{iterations}");
        append_record(&record);
    }
}

fn run_ordered_kleene<
    VarKey: Copy + Eq + Debug + Hash + Default,
    VarValue: PartialOrd + Bottom + Copy,
    S: System<VarKey, VarValue>
        + Arguments<VarKey, HashSet<VarKey>>
        + Universe<HashSet<VarKey>>
        + PairUniverse<HashSet<(VarKey, VarKey)>>
        + Clone,
    O: StrategicLocalOracle<VarKey, VarValue, BinaryHeapStrategy<(VarKey, VarKey)>, S>
        + Display
        + Clone,
>(
    problem: &str,
    name: &str,
    system: &S,
    target: VarKey,
    oracle: &O,
) {
    for _ in 1..=ITERATIONS {
        let oracle = (*oracle).clone();
        let mut system = (*system).clone();
        let (_, iterations) =
            ordered::kleene_local::<_, _, BinaryHeapStrategy<_>, BinaryHeapStrategy<_>, _>(
                &mut system,
                target,
                &oracle,
            );
        let record = format!("{problem},{name},{oracle},true,{iterations}");
        append_record(&record);
    }
}

fn main() {
    if let Err(e) = create_csv() {
        panic!("{e}");
    }

    weak_bisim_oracles! {
        abp_ok: "SPEC", "ABP" => include_str!("../systems/ccs/abp_ok.ccs");
        abpl_ok: "SPEC", "ABPl" => include_str!("../systems/ccs/abp_ok.ccs");
        abpl_ok_2: "SPEC", "ABPl_2" => include_str!("../systems/ccs/abp_ok.ccs");
        abpl_bad_2: "SPEC", "ABPl_2" => include_str!("../systems/ccs/abp_bad.ccs");
        abpl_ok_3: "SPEC", "ABPl_3" => include_str!("../systems/ccs/abp_ok.ccs");
        abpl_bad_3: "SPEC", "ABPl_3" => include_str!("../systems/ccs/abp_bad.ccs");

        // NOTE: these two actually *are* weakly bisimilar, so should not be used
        // abp_bad: "SPEC", "ABP" => include_str!("../systems/ccs/abp_bad.ccs");
        // abpl_bad: "SPEC", "ABPl" => include_str!("../systems/ccs/abp_bad.ccs");

        // TODO: Parameterize on size of leader election?
        leader_election_bad_6: "Spec", "Ring" => r"
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

        leader_election_ok_6: "Spec", "Ring" => r"
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
        dekker_mutual_exclusion: "Dekker-2", "Spec" => r"
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

    wctl_oracles! {
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
