use std::{cell::RefCell, collections::HashMap};

use radguy::{Assignment, System, bislotmap::BiSlotMap};
use slotmap::Key;

use crate::systems::{
    numeric::{number::Number, numeric_system::NumericSystem, numeric_term::NumericTerm},
    wccs::wccs_system::WCCSSystem,
    wctl::flat_formula::{FlatExpr, FlatFormula},
};

pub struct WCTLSystem<'a, ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key> {
    wccs_system: WCCSSystem<'a, ProcKey>,
    numeric_system: RefCell<NumericSystem<VarKey, TermKey, (ProcKey, FormKey)>>,
    pub(crate) formulas: BiSlotMap<FormKey, FlatFormula<'a, FormKey, ExprKey>>,
    pub(crate) expresions: BiSlotMap<ExprKey, FlatExpr<'a, ExprKey>>,
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
        let formula = self.formulas.get_value(formula_key);

        match formula {
            FlatFormula::Const(c) => match c {
                true => self.insert_term(NumericTerm::Const(Number::Val(0))),
                false => self.insert_term(NumericTerm::Const(Number::Inf)),
            },
            FlatFormula::And(left, right) => todo!(),
            FlatFormula::Or(_, _) => todo!(),
            FlatFormula::UniversalUntil { left, right, bound } => todo!(),
            FlatFormula::ExistentialUntil { left, right, bound } => todo!(),
            FlatFormula::UniversalFinally { formula, bound } => todo!(),
            FlatFormula::ExistentialFinally { formula, bound } => todo!(),
            FlatFormula::UniversalNext { formula, bound } => todo!(),
            FlatFormula::SymbolicUniversalUntil { left, right } => todo!(),
            FlatFormula::SymbolicExistentialUntil { left, right } => todo!(),
            FlatFormula::SymbolicUniversalFinally { formula } => todo!(),
            FlatFormula::SymbolicExistentialFinally { formula } => todo!(),
            FlatFormula::ExistentialNext { formula, bound } => todo!(),
            FlatFormula::RelationalExpr(flat_relational_expr) => todo!(),
            FlatFormula::Proposition(_) => todo!(),
        }
    }
}

impl<'a, ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key> System<VarKey, Number>
    for WCTLSystem<'a, ProcKey, FormKey, ExprKey, VarKey, TermKey>
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
