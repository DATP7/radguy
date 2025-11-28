use radguy::arena::Key;

use crate::systems::wccs::wccs_system::MultiSet;
use crate::systems::{numeric::Number, wctl::wctl_system::WCTLSystem};

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum FlatFormula<'a, FormKey: Key, ExprKey: Key> {
    Const(bool),
    And(FormKey, FormKey),
    Or(FormKey, FormKey),
    UniversalUntil {
        left: FormKey,
        right: FormKey,
        bound: Number,
    },
    SymbolicUniversalUntil {
        left: FormKey,
        right: FormKey,
    },
    ExistentialUntil {
        left: FormKey,
        right: FormKey,
        bound: Number,
    },
    SymbolicExistentialUntil {
        left: FormKey,
        right: FormKey,
    },
    UniversalFinally {
        formula: FormKey,
        bound: Number,
    },
    SymbolicUniversalFinally {
        formula: FormKey,
    },
    ExistentialFinally {
        formula: FormKey,
        bound: Number,
    },
    SymbolicExistentialFinally {
        formula: FormKey,
    },
    UniversalNext {
        formula: FormKey,
        bound: Number,
    },
    ExistentialNext {
        formula: FormKey,
        bound: Number,
    },
    RelationalExpr(FlatRelationalExpr<ExprKey>),
    Proposition(&'a str),
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum FlatRelationalExpr<ExprKey: Key> {
    LessThan(ExprKey, ExprKey),
    LessThanEq(ExprKey, ExprKey),
    GreaterThan(ExprKey, ExprKey),
    GreaterThanEq(ExprKey, ExprKey),
    Eq(ExprKey, ExprKey),
    NotEq(ExprKey, ExprKey),
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum FlatExpr<'a, ExprKey: Key> {
    Multiply(ExprKey, ExprKey),
    Add(ExprKey, ExprKey),
    Subtract(ExprKey, ExprKey),
    Divide(ExprKey, ExprKey),
    Inverse(ExprKey),
    Proposition(&'a str),
    Weight(Number),
}

impl<ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key>
    WCTLSystem<'_, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    fn evaluate_expr(&self, process_key: ProcKey, expr_key: ExprKey) -> i64 {
        let expr = self.expresions.borrow().get_value(expr_key).clone();

        match expr {
            FlatExpr::Multiply(l, r) => {
                self.evaluate_expr(process_key, l) * self.evaluate_expr(process_key, r)
            }
            FlatExpr::Add(l, r) => {
                self.evaluate_expr(process_key, l) + self.evaluate_expr(process_key, r)
            }
            FlatExpr::Subtract(l, r) => {
                self.evaluate_expr(process_key, l) - self.evaluate_expr(process_key, r)
            }
            FlatExpr::Divide(l, r) => {
                self.evaluate_expr(process_key, l) / self.evaluate_expr(process_key, r)
            }
            FlatExpr::Inverse(inner) => -self.evaluate_expr(process_key, inner),
            FlatExpr::Proposition(prop) => {
                i64::try_from(self.wccs_system.get_propositions(process_key).count(prop))
                    .expect("Number of propostions should not exceed i64 limits")
            }
            FlatExpr::Weight(number) => match number {
                Number::Val(value) => i64::from(value),
                Number::Inf => panic!("Number in expr can not be infinity"),
            },
        }
    }

    pub(crate) fn evaluate_relexpr(
        &self,
        process_key: ProcKey,
        relexpr: &FlatRelationalExpr<ExprKey>,
    ) -> bool {
        match relexpr {
            FlatRelationalExpr::LessThan(left, right) => {
                self.evaluate_expr(process_key, *left) < self.evaluate_expr(process_key, *right)
            }
            FlatRelationalExpr::LessThanEq(left, right) => {
                self.evaluate_expr(process_key, *left) <= self.evaluate_expr(process_key, *right)
            }
            FlatRelationalExpr::GreaterThan(left, right) => {
                self.evaluate_expr(process_key, *left) > self.evaluate_expr(process_key, *right)
            }
            FlatRelationalExpr::GreaterThanEq(left, right) => {
                self.evaluate_expr(process_key, *left) >= self.evaluate_expr(process_key, *right)
            }
            FlatRelationalExpr::Eq(left, right) => {
                self.evaluate_expr(process_key, *left) == self.evaluate_expr(process_key, *right)
            }
            FlatRelationalExpr::NotEq(left, right) => {
                self.evaluate_expr(process_key, *left) != self.evaluate_expr(process_key, *right)
            }
        }
    }
}
