use std::hash::Hash;
use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap, HashSet},
};

use radguy::extension::TermSystem;
use radguy::{
    Arguments, Assignment, PairUniverse, System, Universe,
    bislotmap::BiSlotMap,
    ordered::strategy::{InitialStrategy, Strategy},
};
use slotmap::Key;

use crate::systems::{
    numeric::{
        number::Number,
        numeric_system::{NumericSystem, NumericSystemImpl},
        numeric_term::NumericTerm,
    },
    wccs::{ast::WeightedAction, wccs_system::WCCSSystem},
    wctl::flat_formula::{FlatExpr, FlatFormula},
};

pub struct WCTLSystem<'a, ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key> {
    pub(crate) wccs_system: WCCSSystem<'a, ProcKey>,
    numeric_system: RefCell<NumericSystemImpl<VarKey, TermKey, (ProcKey, FormKey)>>,
    pub(crate) formulas: RefCell<BiSlotMap<FormKey, FlatFormula<'a, FormKey, ExprKey>>>,
    pub(crate) expresions: RefCell<BiSlotMap<ExprKey, FlatExpr<'a, ExprKey>>>,
}

impl<'a, ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key>
    WCTLSystem<'a, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    pub fn lookup_process_key(&self, process_name: &'a str) -> Option<ProcKey> {
        self.wccs_system.lookup_process_key(process_name)
    }

    pub fn new(wccs_system: WCCSSystem<'a, ProcKey>) -> Self {
        WCTLSystem {
            wccs_system,
            numeric_system: RefCell::new(NumericSystemImpl::default()),
            formulas: RefCell::new(BiSlotMap::default()),
            expresions: RefCell::new(BiSlotMap::default()),
        }
    }
    fn insert_term(&self, term: NumericTerm<VarKey, TermKey>) -> TermKey {
        self.numeric_system
            .borrow_mut()
            .terms
            .get_or_insert_key(term)
    }

    fn get_term_key(&self, var_key: VarKey) -> TermKey {
        if let Some(term_key) = self.numeric_system.borrow().definitions.get(var_key) {
            return *term_key;
        }

        let (process_key, formula_key) = *self.numeric_system.borrow().names.get_value(var_key);
        let formula = self.formulas.borrow().get_value(formula_key).clone();

        let term_key = match formula {
            FlatFormula::Const(c) => {
                if c {
                    self.insert_term(NumericTerm::Const(Number::Val(0)))
                } else {
                    self.insert_term(NumericTerm::Const(Number::Inf))
                }
            }
            FlatFormula::And(left, right) => {
                let left_var_key = self.get_var(process_key, left);
                let right_var_key = self.get_var(process_key, right);

                let left_term = self.insert_term(NumericTerm::Var(left_var_key));
                let right_term = self.insert_term(NumericTerm::Var(right_var_key));
                self.insert_term(NumericTerm::Max(BTreeSet::from([left_term, right_term])))
            }
            FlatFormula::Or(left, right) => {
                let left_var_key = self.get_var(process_key, left);
                let right_var_key = self.get_var(process_key, right);

                let left_term = self.insert_term(NumericTerm::Var(left_var_key));
                let right_term = self.insert_term(NumericTerm::Var(right_var_key));
                self.insert_term(NumericTerm::Min(BTreeSet::from([left_term, right_term])))
            }
            FlatFormula::UniversalUntil { left, right, bound } => {
                let symbolic_formula = FlatFormula::SymbolicUniversalUntil { left, right };
                self.cover_edge(bound, process_key, symbolic_formula)
            }
            FlatFormula::ExistentialUntil { left, right, bound } => {
                let symbolic_formula = FlatFormula::SymbolicExistentialUntil { left, right };
                self.cover_edge(bound, process_key, symbolic_formula)
            }
            FlatFormula::UniversalFinally { formula, bound } => {
                let symbolic_formula = FlatFormula::SymbolicUniversalFinally { formula };
                self.cover_edge(bound, process_key, symbolic_formula)
            }
            FlatFormula::ExistentialFinally { formula, bound } => {
                let symbolic_formula = FlatFormula::SymbolicExistentialFinally { formula };
                self.cover_edge(bound, process_key, symbolic_formula)
            }
            FlatFormula::UniversalNext { formula, bound } => {
                let transitions = self.flatten_transitions(process_key);
                let sub_terms =
                    transitions
                        .filter(|(weight, _)| *weight <= bound)
                        .map(|(_, succ_proc)| {
                            let var_key = self.get_var(succ_proc, formula);
                            self.insert_term(NumericTerm::Var(var_key))
                        });
                self.insert_term(NumericTerm::Max(sub_terms.collect()))
            }
            FlatFormula::ExistentialNext { formula, bound } => {
                let transitions = self.flatten_transitions(process_key);
                let sub_terms =
                    transitions
                        .filter(|(weight, _)| *weight <= bound)
                        .map(|(_, succ_proc)| {
                            let var_key = self.get_var(succ_proc, formula);
                            self.insert_term(NumericTerm::Var(var_key))
                        });
                self.insert_term(NumericTerm::Min(sub_terms.collect()))
            }
            FlatFormula::SymbolicUniversalUntil { left, right } => {
                let transitions = self.flatten_transitions(process_key);
                let mut hyper_edge: BTreeSet<TermKey> = transitions
                    .map(|(weight, proc)| {
                        let sub_var = self.get_var(proc, formula_key);
                        let sub_term = self.insert_term(NumericTerm::Var(sub_var));
                        let weight_term = self.insert_term(NumericTerm::Const(weight));
                        self.insert_term(NumericTerm::Add(weight_term, sub_term))
                    })
                    .collect();

                let left_term = self.insert_term(NumericTerm::Var(self.get_var(process_key, left)));
                let right_term =
                    self.insert_term(NumericTerm::Var(self.get_var(process_key, right)));

                hyper_edge.insert(left_term);

                let hyper_edge = self.insert_term(NumericTerm::Max(hyper_edge));

                self.insert_term(NumericTerm::Min(BTreeSet::from([right_term, hyper_edge])))
            }
            FlatFormula::SymbolicExistentialUntil { left, right } => {
                let left_term = self.insert_term(NumericTerm::Var(self.get_var(process_key, left)));
                let right_term =
                    self.insert_term(NumericTerm::Var(self.get_var(process_key, right)));

                let transitions = self.flatten_transitions(process_key);
                let mut hyper_edges: BTreeSet<TermKey> = transitions
                    .map(|(weight, proc)| {
                        let sub_var = self.get_var(proc, formula_key);
                        let sub_term = self.insert_term(NumericTerm::Var(sub_var));
                        let weight_term = self.insert_term(NumericTerm::Const(weight));
                        let add_term = self.insert_term(NumericTerm::Add(weight_term, sub_term));

                        self.insert_term(NumericTerm::Max(BTreeSet::from([left_term, add_term])))
                    })
                    .collect();

                hyper_edges.insert(right_term);

                self.insert_term(NumericTerm::Min(hyper_edges))
            }
            FlatFormula::SymbolicUniversalFinally {
                formula: acceptance_formula,
            } => {
                let transitions = self.flatten_transitions(process_key);
                let hyper_edge: BTreeSet<TermKey> = transitions
                    .map(|(weight, proc)| {
                        let sub_var = self.get_var(proc, formula_key);
                        let sub_term = self.insert_term(NumericTerm::Var(sub_var));
                        let weight_term = self.insert_term(NumericTerm::Const(weight));
                        self.insert_term(NumericTerm::Add(weight_term, sub_term))
                    })
                    .collect();

                let acceptance_term = self.insert_term(NumericTerm::Var(
                    self.get_var(process_key, acceptance_formula),
                ));
                let hyper_edge = self.insert_term(NumericTerm::Max(hyper_edge));

                self.insert_term(NumericTerm::Min(BTreeSet::from([
                    acceptance_term,
                    hyper_edge,
                ])))
            }

            FlatFormula::SymbolicExistentialFinally {
                formula: acceptance_formula,
            } => {
                let transitions = self.flatten_transitions(process_key);
                let mut hyper_edges: BTreeSet<TermKey> = transitions
                    .map(|(weight, proc)| {
                        let sub_var = self.get_var(proc, formula_key);
                        let sub_term = self.insert_term(NumericTerm::Var(sub_var));
                        let weight_term = self.insert_term(NumericTerm::Const(weight));
                        self.insert_term(NumericTerm::Add(weight_term, sub_term))
                    })
                    .collect();

                let acceptance_term = self.insert_term(NumericTerm::Var(
                    self.get_var(process_key, acceptance_formula),
                ));

                hyper_edges.insert(acceptance_term);

                self.insert_term(NumericTerm::Min(hyper_edges))
            }
            FlatFormula::RelationalExpr(flat_relational_expr) => {
                if self.evaluate_relexpr(process_key, &flat_relational_expr) {
                    self.insert_term(NumericTerm::Const(Number::Val(0)))
                } else {
                    self.insert_term(NumericTerm::Const(Number::Inf))
                }
            }
            FlatFormula::Proposition(prop) => {
                if self
                    .wccs_system
                    .get_propositions(process_key)
                    .contains(&prop)
                {
                    self.insert_term(NumericTerm::Const(Number::Val(0)))
                } else {
                    self.insert_term(NumericTerm::Const(Number::Inf))
                }
            }
        };

        self.numeric_system
            .borrow_mut()
            .definitions
            .insert(var_key, term_key);

        term_key
    }

    fn flatten_transitions(&self, process_key: ProcKey) -> impl Iterator<Item = (Number, ProcKey)> {
        let transitions = self.wccs_system.get_transitions(process_key);
        transitions
            .into_iter()
            .flat_map(move |(WeightedAction { weight, .. }, successors)| {
                successors
                    .into_iter()
                    .map(move |succ_proc| (weight, succ_proc))
            })
    }

    pub fn get_var(&self, process_key: ProcKey, formula_key: FormKey) -> VarKey {
        self.numeric_system
            .borrow_mut()
            .names
            .get_or_insert_key((process_key, formula_key))
    }

    fn cover_edge(
        &self,
        bound: Number,
        process_key: ProcKey,
        symbolic_formula: FlatFormula<'a, FormKey, ExprKey>,
    ) -> TermKey {
        let symbolic_formula_key = self
            .formulas
            .borrow_mut()
            .get_or_insert_key(symbolic_formula);

        let var_key = self
            .numeric_system
            .borrow_mut()
            .names
            .get_or_insert_key((process_key, symbolic_formula_key));

        let symbolic_term_key = self.insert_term(NumericTerm::Var(var_key));
        self.insert_term(NumericTerm::Bound {
            bound,
            term: symbolic_term_key,
        })
    }
}

impl<ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key> System<VarKey, Number>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn evaluate(&self, key: VarKey, assignment: &dyn Assignment<VarKey, Number>) -> Number {
        let term_key = self.get_term_key(key);
        self.numeric_system
            .borrow()
            .evaluate_term(term_key, assignment)
    }

    fn bottom_assignment(&self) -> impl Assignment<VarKey, Number> {
        HashMap::new()
    }
}

impl<ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key>
    Arguments<VarKey, HashSet<VarKey>>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn arguments(&self, key: VarKey) -> HashSet<VarKey> {
        let term_key = self.get_term_key(key);
        self.numeric_system.borrow().term_arguments(term_key)
    }
}

impl<ProcKey: Key, VarKey: Key, TermKey: Key, FormKey: Key, ExprKey: Key> Universe<HashSet<VarKey>>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn universe(&self) -> HashSet<VarKey> {
        self.numeric_system.borrow().universe()
    }
}

impl<ProcKey: Key, VarKey: Key, TermKey: Key, FormKey: Key, ExprKey: Key>
    PairUniverse<HashSet<(VarKey, VarKey)>>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn pair_universe(&self) -> HashSet<(VarKey, VarKey)> {
        self.numeric_system.borrow().pair_universe()
    }
}

impl<ProcKey, VarKey, TermKey, FormKey, ExprKey, OutStrategy>
    InitialStrategy<VarKey, Number, OutStrategy>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
where
    NumericSystemImpl<VarKey, TermKey, (ProcKey, FormKey)>:
        InitialStrategy<VarKey, Number, OutStrategy>,
    ProcKey: Key,
    VarKey: Key + Clone + Hash,
    TermKey: Key + Hash,
    FormKey: Key,
    ExprKey: Key,
    OutStrategy: Strategy<(VarKey, VarKey)>,
{
    fn get_initial_strategy(&self) -> OutStrategy {
        self.numeric_system.borrow().get_initial_strategy()
    }
}

impl<ProcKey: Key, VarKey: Key, TermKey: Key, FormKey: Key, ExprKey: Key>
    TermSystem<VarKey, Number, TermKey>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn definition(&self, variable: VarKey) -> TermKey {
        self.get_term_key(variable)
    }
}

impl<ProcKey: Key, VarKey: Key, TermKey: Key, FormKey: Key, ExprKey: Key>
    NumericSystem<VarKey, TermKey, (ProcKey, FormKey)>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn get_term(&self, term_key: TermKey) -> NumericTerm<VarKey, TermKey> {
        self.numeric_system.borrow().get_term(term_key)
    }

    fn evaluate_term(
        &self,
        term_key: TermKey,
        assignment: &dyn Assignment<VarKey, Number>,
    ) -> Number {
        self.numeric_system
            .borrow()
            .evaluate_term(term_key, assignment)
    }
}
