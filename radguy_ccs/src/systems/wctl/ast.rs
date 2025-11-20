use slotmap::Key;

use crate::systems::{
    numeric::Number,
    wctl::{
        flat_formula::{FlatExpr, FlatFormula, FlatRelationalExpr},
        wctl_system::WCTLSystem,
    },
};

#[derive(Clone)]
pub enum Formula<'a> {
    Const(bool),
    And(Box<Formula<'a>>, Box<Formula<'a>>),
    Or(Box<Formula<'a>>, Box<Formula<'a>>),
    UniversalUntil {
        left: Box<Formula<'a>>,
        right: Box<Formula<'a>>,
        bound: Number,
    },
    ExistentialUntil {
        left: Box<Formula<'a>>,
        right: Box<Formula<'a>>,
        bound: Number,
    },
    UniversalFinally {
        formula: Box<Formula<'a>>,
        bound: Number,
    },
    ExistentialFinally {
        formula: Box<Formula<'a>>,
        bound: Number,
    },
    UniversalNext {
        formula: Box<Formula<'a>>,
        bound: Number,
    },
    ExistentialNext {
        formula: Box<Formula<'a>>,
        bound: Number,
    },
    RelationalExpr(RelationalExpr<'a>),
    Proposition(&'a str),
}

#[derive(Clone)]
pub enum RelationalExpr<'a> {
    LessThan(Box<Expr<'a>>, Box<Expr<'a>>),
    LessThanEq(Box<Expr<'a>>, Box<Expr<'a>>),
    GreaterThan(Box<Expr<'a>>, Box<Expr<'a>>),
    GreaterThanEq(Box<Expr<'a>>, Box<Expr<'a>>),
    Eq(Box<Expr<'a>>, Box<Expr<'a>>),
    NotEq(Box<Expr<'a>>, Box<Expr<'a>>),
}

#[derive(Clone)]
pub enum Expr<'a> {
    Multiply(Box<Expr<'a>>, Box<Expr<'a>>),
    Add(Box<Expr<'a>>, Box<Expr<'a>>),
    Subtract(Box<Expr<'a>>, Box<Expr<'a>>),
    Divide(Box<Expr<'a>>, Box<Expr<'a>>),
    Inverse(Box<Expr<'a>>),
    Proposition(&'a str),
    Weight(Number),
}

impl<'a, ProcKey: Key, FormKey: Key, ExprKey: Key, VarKey: Key, TermKey: Key>
    WCTLSystem<'a, ProcKey, FormKey, ExprKey, VarKey, TermKey>
{
    pub fn insert_ast_formula(&self, formula: Formula<'a>) -> FormKey {
        match formula {
            Formula::Const(bool) => self.insert_formula(FlatFormula::Const(bool)),
            Formula::And(left, right) => {
                let left = self.insert_ast_formula(*left);
                let right = self.insert_ast_formula(*right);
                self.insert_formula(FlatFormula::And(right, left))
            }
            Formula::Or(left, right) => {
                let left = self.insert_ast_formula(*left);
                let right = self.insert_ast_formula(*right);
                self.insert_formula(FlatFormula::Or(right, left))
            }
            Formula::UniversalUntil { left, right, bound } => {
                let left = self.insert_ast_formula(*left);
                let right = self.insert_ast_formula(*right);
                self.insert_formula(FlatFormula::UniversalUntil { right, left, bound })
            }
            Formula::ExistentialUntil { left, right, bound } => {
                let left = self.insert_ast_formula(*left);
                let right = self.insert_ast_formula(*right);
                self.insert_formula(FlatFormula::ExistentialUntil { right, left, bound })
            }
            Formula::UniversalFinally { formula, bound } => {
                let formula = self.insert_ast_formula(*formula);
                self.insert_formula(FlatFormula::UniversalFinally { formula, bound })
            }
            Formula::ExistentialFinally { formula, bound } => {
                let formula = self.insert_ast_formula(*formula);
                self.insert_formula(FlatFormula::ExistentialFinally { formula, bound })
            }
            Formula::UniversalNext { formula, bound } => {
                let formula = self.insert_ast_formula(*formula);
                self.insert_formula(FlatFormula::UniversalNext { formula, bound })
            }
            Formula::ExistentialNext { formula, bound } => {
                let formula = self.insert_ast_formula(*formula);
                self.insert_formula(FlatFormula::ExistentialNext { formula, bound })
            }
            Formula::RelationalExpr(relational_expr) => {
                let relational_expr = self.convert_relational_expr(relational_expr);
                self.insert_formula(FlatFormula::RelationalExpr(relational_expr))
            }
            Formula::Proposition(prop) => self.insert_formula(FlatFormula::Proposition(prop)),
        }
    }

    fn convert_relational_expr(&self, relexpr: RelationalExpr<'a>) -> FlatRelationalExpr<ExprKey> {
        match relexpr {
            RelationalExpr::LessThan(left, right) => {
                let left = self.insert_ast_expr(*left);
                let right = self.insert_ast_expr(*right);
                FlatRelationalExpr::LessThan(left, right)
            }
            RelationalExpr::LessThanEq(left, right) => {
                let left = self.insert_ast_expr(*left);
                let right = self.insert_ast_expr(*right);
                FlatRelationalExpr::LessThanEq(left, right)
            }
            RelationalExpr::GreaterThan(left, right) => {
                let left = self.insert_ast_expr(*left);
                let right = self.insert_ast_expr(*right);
                FlatRelationalExpr::GreaterThan(left, right)
            }
            RelationalExpr::GreaterThanEq(left, right) => {
                let left = self.insert_ast_expr(*left);
                let right = self.insert_ast_expr(*right);
                FlatRelationalExpr::GreaterThanEq(left, right)
            }
            RelationalExpr::Eq(left, right) => {
                let left = self.insert_ast_expr(*left);
                let right = self.insert_ast_expr(*right);
                FlatRelationalExpr::Eq(left, right)
            }
            RelationalExpr::NotEq(left, right) => {
                let left = self.insert_ast_expr(*left);
                let right = self.insert_ast_expr(*right);
                FlatRelationalExpr::NotEq(left, right)
            }
        }
    }

    fn insert_ast_expr(&self, expr: Expr<'a>) -> ExprKey {
        match expr {
            Expr::Multiply(left, right) => {
                let left = self.insert_ast_expr(*left);
                let right = self.insert_ast_expr(*right);
                self.insert_expr(FlatExpr::Multiply(left, right))
            }
            Expr::Add(left, right) => {
                let left = self.insert_ast_expr(*left);
                let right = self.insert_ast_expr(*right);
                self.insert_expr(FlatExpr::Add(left, right))
            }
            Expr::Subtract(left, right) => {
                let left = self.insert_ast_expr(*left);
                let right = self.insert_ast_expr(*right);
                self.insert_expr(FlatExpr::Subtract(left, right))
            }
            Expr::Divide(left, right) => {
                let left = self.insert_ast_expr(*left);
                let right = self.insert_ast_expr(*right);
                self.insert_expr(FlatExpr::Divide(left, right))
            }
            Expr::Inverse(expr) => {
                let expr = self.insert_ast_expr(*expr);
                self.insert_expr(FlatExpr::Inverse(expr))
            }
            Expr::Proposition(prop) => self.insert_expr(FlatExpr::Proposition(prop)),
            Expr::Weight(number) => self.insert_expr(FlatExpr::Weight(number)),
        }
    }
    fn insert_formula(&self, formula: FlatFormula<'a, FormKey, ExprKey>) -> FormKey {
        self.formulas.borrow_mut().get_or_insert_key(formula)
    }

    fn insert_expr(&self, expr: FlatExpr<'a, ExprKey>) -> ExprKey {
        self.expresions.borrow_mut().get_or_insert_key(expr)
    }
}

#[cfg(test)]
mod tests {
    use crate::systems::wctl::grammar::DeclarationParser;
    use crate::{assert_bad, assert_good};

    #[test]
    fn test_parse_func() {
        let parser = DeclarationParser::new();

        let good = [
            "T = tt",                   // Const
            "T = true",                 // Const
            "T = True",                 // Const
            "T = ff",                   // Const
            "T = false",                // Const
            "T = False",                // Const
            "T = mow",                  // Prop
            "T = true && true",         // And
            "T = true and true",        // And
            "T = true || true",         // Or
            "T = true or true",         // Or
            "T = A true U false",       // Universal Until
            "T = A true U [<=8] false", // Universal Until Bounded
            "T = E true U false",       // Existential Until
            "T = E true U [<=8] false", // Existential Until Bounded
            "T = AF true",              // Universal Finally
            "T = AF[<=8] true",         // Universal Finally Bounded
            "T = EF true",              // Existential Finally
            "T = EF[<=8] true",         // Existential Finally Bounded
            "T = AX true",              // Universal Next
            "T = AX[<=8] true",         // Universal Next Bounded
            "T = EX true",              // Existential Next
            "T = EX[<=8] true",         // Existential Next Bounded
            "T = x < y",                // Comparison
            "T = x <= y",               // Comparison
            "T = x == y",               // Comparison
            "T = x != y",               // Comparison
            "T = x >= y",               // Comparison
            "T = x > y",                // Comparison
            "T = a * 3 == b + 2",       // Expresions
            "T = a * 3 == -2",          // Expresions
            "T = a * 3 == -b",          // Expresions
            "T = a / 3 == -b",          // Expresions
        ];

        let bad = [
            "T = ",
            "T != tf",
            "T := tf",
            "T == tf",
            "T = A false",
            "T = A true U [<=] false",
            "T = A true U [<=x] false",
            "T = A tf U [<=x] false",
            "T = x < ==",
            "T = 3 || 4",
            "T = 3 && 4",
            "T = E true 3",
            "T = DX[<=8] true",
            "T = DX true",
            "T = a / 3 = -b",
        ];

        assert_good!(good, parser);
        assert_bad!(bad, parser);
    }
}
