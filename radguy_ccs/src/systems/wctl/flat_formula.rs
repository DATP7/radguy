use slotmap::Key;

use crate::systems::numeric::number::Number;

#[derive(Hash, PartialEq, Eq, Clone)]
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

#[derive(Hash, PartialEq, Eq, Clone)]
pub enum FlatRelationalExpr<ExprKey: Key> {
    LessThan(ExprKey, ExprKey),
    LessThanEq(ExprKey, ExprKey),
    GreaterThan(ExprKey, ExprKey),
    GreaterThanEq(ExprKey, ExprKey),
    Eq(ExprKey, ExprKey),
    NotEq(ExprKey, ExprKey),
}

#[derive(Hash, PartialEq, Eq, Clone)]
pub enum FlatExpr<'a, ExprKey: Key> {
    Multiply(ExprKey, ExprKey),
    Add(ExprKey, ExprKey),
    Subtract(ExprKey, ExprKey),
    Divide(ExprKey, ExprKey),
    Inverse(ExprKey),
    Proposition(&'a str),
    Weight(Number),
}
