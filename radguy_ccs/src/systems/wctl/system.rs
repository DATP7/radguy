use std::{
    cell::RefCell,
    collections::{BTreeSet, HashMap},
};

use radguy::{Assignment, System, bislotmap::BiSlotMap};
use slotmap::Key;

use crate::systems::{
    numeric::{number::Number, numeric_system::NumericSystem, numeric_term::NumericTerm},
    wccs::{ast::WeightedAction, wccs_system::WCCSSystem},
    wctl::flat_formula::{FlatExpr, FlatFormula},
};

pub struct WCTLSystem<'a, ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key> {
    wccs_system: WCCSSystem<'a, ProcKey>,
    numeric_system: RefCell<NumericSystem<VarKey, TermKey, (ProcKey, FormKey)>>,
    pub(crate) formulas: RefCell<BiSlotMap<FormKey, FlatFormula<'a, FormKey, ExprKey>>>,
    pub(crate) expresions: RefCell<BiSlotMap<ExprKey, FlatExpr<'a, ExprKey>>>,
}

impl<'a, ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key>
    WCTLSystem<'a, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn insert_term(&self, term: NumericTerm<VarKey, TermKey>) -> TermKey {
        self.numeric_system
            .borrow_mut()
            .terms
            .get_or_insert_key(term)
    }

    fn get_term(&self, key: VarKey, assignment: &dyn Assignment<VarKey, Number>) -> TermKey {
        if let Some(term_key) = self.numeric_system.borrow().definitions.get(key) {
            return *term_key;
        }

        let (process_key, formula_key) = *self.numeric_system.borrow().names.get_value(key);
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

                let left_term = self.get_term(left_var_key, assignment);
                let right_term = self.get_term(right_var_key, assignment);
                self.insert_term(NumericTerm::Max(BTreeSet::from([left_term, right_term])))
            }
            FlatFormula::Or(left, right) => {
                let left_var_key = self.get_var(process_key, left);
                let right_var_key = self.get_var(process_key, right);

                let left_term = self.get_term(left_var_key, assignment);
                let right_term = self.get_term(right_var_key, assignment);
                self.insert_term(NumericTerm::Min(BTreeSet::from([left_term, right_term])))
            }
            FlatFormula::UniversalUntil { left, right, bound } => {
                let symbolic_formula = FlatFormula::SymbolicUniversalUntil { left, right };
                self.cover_edge(bound, process_key, symbolic_formula, assignment)
            }
            FlatFormula::ExistentialUntil { left, right, bound } => {
                let symbolic_formula = FlatFormula::SymbolicExistentialUntil { left, right };
                self.cover_edge(bound, process_key, symbolic_formula, assignment)
            }
            FlatFormula::UniversalFinally { formula, bound } => {
                let symbolic_formula = FlatFormula::SymbolicUniversalFinally { formula };
                self.cover_edge(bound, process_key, symbolic_formula, assignment)
            }
            FlatFormula::ExistentialFinally { formula, bound } => {
                let symbolic_formula = FlatFormula::SymbolicExistentialFinally { formula };
                self.cover_edge(bound, process_key, symbolic_formula, assignment)
            }
            FlatFormula::UniversalNext { formula, bound } => {
                let sub_terms = self.get_bounded_subterms(process_key, formula, bound, assignment);
                self.insert_term(NumericTerm::Max(sub_terms))
            }
            FlatFormula::ExistentialNext { formula, bound } => {
                let sub_terms = self.get_bounded_subterms(process_key, formula, bound, assignment);
                self.insert_term(NumericTerm::Min(sub_terms))
            }
            FlatFormula::SymbolicUniversalUntil { left, right } => todo!(),
            FlatFormula::SymbolicExistentialUntil { left, right } => todo!(),
            FlatFormula::SymbolicUniversalFinally { formula } => todo!(),

            FlatFormula::SymbolicExistentialFinally { formula } => todo!(),
            FlatFormula::RelationalExpr(flat_relational_expr) => todo!(),
            FlatFormula::Proposition(_) => todo!(),
        };

        self.numeric_system
            .borrow_mut()
            .definitions
            .insert(key, term_key);

        term_key
    }

    fn get_bounded_subterms(
        &self,
        process_key: ProcKey,
        formula: FormKey,
        bound: Number,
        assignment: &dyn Assignment<VarKey, Number>,
    ) -> BTreeSet<TermKey> {
        let transitions = self.wccs_system.get_transitions(process_key);
        transitions
            .into_iter()
            .filter(|(WeightedAction { weight, .. }, _)| *weight <= bound)
            .flat_map(|(_, successors)| {
                successors.into_iter().map(|succ_proc| {
                    let var_key = self.get_var(succ_proc, formula);
                    self.get_term(var_key, assignment)
                })
            })
            .collect()
    }

    fn get_var(&self, process_key: ProcKey, formula_key: FormKey) -> VarKey {
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
        assignment: &dyn Assignment<VarKey, Number>,
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

        let symbolic_term_key = self.get_term(var_key, assignment);
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
        let Some(term_key) = self.numeric_system.borrow().definitions.get(key) else {
            todo!()
        };

        todo!()
    }

    fn bottom_assignment(&self) -> impl Assignment<VarKey, Number> {
        HashMap::new()
    }
}
