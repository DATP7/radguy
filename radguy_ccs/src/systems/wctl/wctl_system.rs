use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap, HashSet},
};

use radguy::{
    Arguments, DependencyGraphSystem, PairUniverse, System, Universe, Visited,
    arena::{BiArena, Key, SecondaryArena},
    extension::TermSystem,
};

use crate::systems::{
    numeric::{
        Number, NumericTerm,
        numeric_system::{NumericSystem, NumericSystemImpl},
    },
    wccs::{ast::WeightedAction, wccs_system::WCCSSystem},
    wctl::flat_formula::{FlatExpr, FlatFormula},
};

type HyperedgeMap<VarKey> = SecondaryArena<VarKey, Vec<Vec<(VarKey, Number)>>>;

#[derive(Debug, Clone)]
pub struct WCTLSystem<'a, ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key> {
    pub(crate) wccs_system: WCCSSystem<'a, ProcKey>,
    numeric_system: RefCell<NumericSystemImpl<VarKey, TermKey, (ProcKey, FormKey)>>,
    pub(crate) formulas: RefCell<BiArena<FormKey, FlatFormula<'a, FormKey, ExprKey>>>,
    pub(crate) expresions: RefCell<BiArena<ExprKey, FlatExpr<'a, ExprKey>>>,
    locked: bool,
    hyper_edge_cache: RefCell<HyperedgeMap<VarKey>>,
    target: Option<VarKey>,
}
impl<'a, ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key>
    WCTLSystem<'a, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    pub fn get_process_definition(&self, process_name: &'a str) -> Option<ProcKey> {
        self.wccs_system.get_definition(process_name)
    }

    pub const fn set_target(&mut self, target: VarKey) {
        self.target = Some(target);
    }

    pub fn new(wccs_system: WCCSSystem<'a, ProcKey>) -> Self {
        WCTLSystem {
            wccs_system,
            numeric_system: RefCell::new(NumericSystemImpl::default()),
            formulas: RefCell::new(BiArena::default()),
            expresions: RefCell::new(BiArena::default()),
            locked: false,
            hyper_edge_cache: RefCell::default(),
            target: None,
        }
    }
    fn insert_term(&self, term: NumericTerm<VarKey, TermKey>) -> TermKey {
        self.numeric_system
            .borrow_mut()
            .terms
            .get_or_insert_key(term)
    }

    fn get_definition(&self, var_key: VarKey) -> TermKey {
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

    /// Formats the transitions from WCCS so actions are discardet and the map is flatternd to pairs of (w, p)
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

macro_rules! assert_access_allowed {
    ($self:expr, $key:expr) => {
        debug_assert!(
            !$self.locked || $self.numeric_system.borrow().definitions.contains_key($key),
            "Variable {:?} was visited for the first time while the system was locked",
            $self.numeric_system.borrow().names.get_value($key)
        )
    };
}

impl<ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key> System<VarKey, Number>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn evaluate(&self, key: VarKey, assignment: &HashMap<VarKey, Number>) -> Number {
        assert_access_allowed!(self, key);
        let term_key = self.get_definition(key);
        self.numeric_system
            .borrow()
            .evaluate_term(term_key, assignment)
    }

    fn bottom_assignment(&self) -> HashMap<VarKey, Number> {
        HashMap::new()
    }

    fn lock(&mut self) {
        self.locked = true;
    }

    fn unlock(&mut self) {
        self.locked = false;
    }

    fn target(&self) -> Option<VarKey> {
        self.target
    }
}
impl<ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key, S> Visited<S>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
where
    NumericSystemImpl<VarKey, TermKey, (ProcKey, FormKey)>: Visited<S>,
{
    fn visited(&self) -> S {
        self.numeric_system.borrow().visited()
    }
}

impl<ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key>
    Arguments<VarKey, HashSet<VarKey>>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn arguments(&self, key: VarKey) -> HashSet<VarKey> {
        assert_access_allowed!(self, key);
        let term_key = self.get_definition(key);
        self.numeric_system.borrow().term_arguments(term_key)
    }
}

impl<ProcKey: Key, VarKey: Key, TermKey: Key, FormKey: Key, ExprKey: Key, S> Universe<S>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
where
    NumericSystemImpl<VarKey, TermKey, (ProcKey, FormKey)>: Universe<S>,
{
    fn universe(&self) -> S {
        self.numeric_system.borrow().universe()
    }
}

impl<ProcKey: Key, VarKey: Key, TermKey: Key, FormKey: Key, ExprKey: Key, S> PairUniverse<S>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
where
    NumericSystemImpl<VarKey, TermKey, (ProcKey, FormKey)>: PairUniverse<S>,
{
    fn pair_universe(&self) -> S {
        self.numeric_system.borrow().pair_universe()
    }
}

impl<ProcKey: Key, VarKey: Key, TermKey: Key, FormKey: Key, ExprKey: Key>
    TermSystem<VarKey, Number, TermKey>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn definition(&self, variable: VarKey) -> TermKey {
        assert_access_allowed!(self, variable);
        self.get_definition(variable)
    }
}

impl<ProcKey: Key, VarKey: Key, TermKey: Key, FormKey: Key, ExprKey: Key>
    NumericSystem<VarKey, TermKey, (ProcKey, FormKey)>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn get_term(&self, term_key: TermKey) -> NumericTerm<VarKey, TermKey> {
        self.numeric_system.borrow().get_term(term_key)
    }

    fn evaluate_term(&self, term_key: TermKey, assignment: &HashMap<VarKey, Number>) -> Number {
        self.numeric_system
            .borrow()
            .evaluate_term(term_key, assignment)
    }
}

impl<ProcKey: Key, VarKey: Key, TermKey: Key, FormKey: Key, ExprKey: Key>
    WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn get_var_key_of_sum(&self, term_key: TermKey) -> Option<VarKey> {
        match self.get_term(term_key) {
            NumericTerm::Var(var_key) => Some(var_key),
            NumericTerm::Add(left_term, right_term) => self
                .get_var_key_of_sum(right_term)
                .or_else(|| self.get_var_key_of_sum(left_term)),
            _ => None,
        }
    }

    fn get_weight_of_sum(&self, term_key: TermKey) -> Option<Number> {
        match self.get_term(term_key) {
            NumericTerm::Const(weight) => Some(weight),
            NumericTerm::Add(left_term, right_term) => self
                .get_weight_of_sum(left_term)
                .or_else(|| self.get_weight_of_sum(right_term)),
            NumericTerm::Var(_) => None,
            _ => unreachable!("Hyper edge targets should always be a var or an add"),
        }
    }

    fn get_weighted_hyperedge(&self, term_key: TermKey) -> Vec<(VarKey, Number)> {
        match self.get_term(term_key) {
            NumericTerm::Var(var_key) => Vec::from([(var_key, Number::Val(0))]),
            NumericTerm::Add(_, _) => Vec::from([(
                self.get_var_key_of_sum(term_key)
                    .expect("target should contain a variable"),
                self.get_weight_of_sum(term_key).unwrap_or(Number::Val(0)),
            )]),
            NumericTerm::Max(elements) => elements
                .into_iter()
                .map(|term_key| {
                    (
                        self.get_var_key_of_sum(term_key)
                            .expect("target should contain a variable"),
                        self.get_weight_of_sum(term_key).unwrap_or(Number::Val(0)),
                    )
                })
                .collect(),
            _ => unreachable!("A hyper edge is either a max of targets or a target (var or add)"),
        }
    }

    fn get_weighted_hyperedges(&self, key: VarKey) -> Option<Vec<Vec<(VarKey, Number)>>> {
        if let Some(hyperedge) = self.hyper_edge_cache.borrow().get(key) {
            return Some(hyperedge.clone());
        }

        let term_key = *self.numeric_system.borrow().definitions.get(key)?;

        let term = self.get_term(term_key);

        let hyperedge: Vec<Vec<(VarKey, Number)>> = match term {
            NumericTerm::Const(_) => Vec::new(),
            NumericTerm::Min(elements) => elements
                .into_iter()
                .map(|term_key| self.get_weighted_hyperedge(term_key))
                .collect(),
            NumericTerm::Max(_) => Vec::from([self.get_weighted_hyperedge(term_key)]),
            NumericTerm::Bound { term: term_key, .. } => {
                Vec::from([self.get_weighted_hyperedge(term_key)])
            }
            _ => unreachable!("A hyperedge collection can only be a Const, Min, Max or Bound"),
        };

        self.hyper_edge_cache
            .borrow_mut()
            .insert(key, hyperedge.clone());

        Some(hyperedge)
    }
}

impl<ProcKey: Key, VarKey: Key, TermKey: Key, FormKey: Key, ExprKey: Key>
    DependencyGraphSystem<VarKey, VarKey>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn get_hyperedges(&self, key: VarKey) -> Option<Vec<Vec<VarKey>>> {
        self.get_weighted_hyperedges(key).map(|some| {
            some.into_iter()
                .map(|hyperedge| hyperedge.into_iter().map(|(var_key, _)| var_key).collect())
                .collect()
        })
    }
}

impl<ProcKey: Key, VarKey: Key, TermKey: Key, FormKey: Key, ExprKey: Key>
    DependencyGraphSystem<VarKey, (VarKey, Number)>
    for WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn get_hyperedges(&self, key: VarKey) -> Option<Vec<Vec<(VarKey, Number)>>> {
        self.get_weighted_hyperedges(key)
    }
}
