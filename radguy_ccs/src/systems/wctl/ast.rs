pub enum Formula<'a> {
    Const(bool),
    And(Box<Formula<'a>>, Box<Formula<'a>>),
    Or(Box<Formula<'a>>, Box<Formula<'a>>),
    UniversalUntil {
        left: Box<Formula<'a>>,
        right: Box<Formula<'a>>,
        bound: Weight,
    },
    ExistentialUntil {
        left: Box<Formula<'a>>,
        right: Box<Formula<'a>>,
        bound: Weight,
    },
    UniversalFinally {
        formula: Box<Formula<'a>>,
        bound: Weight,
    },
    ExistentialFinally {
        formula: Box<Formula<'a>>,
        bound: Weight,
    },
    UniversalNext {
        formula: Box<Formula<'a>>,
        bound: Weight,
    },
    ExistentialNext {
        formula: Box<Formula<'a>>,
        bound: Weight,
    },
    RelationalExpr(RelationalExpr<'a>),
    Proposition(&'a str),
}

pub enum Weight {
    Val(i32),
    Inf,
}

pub enum RelationalExpr<'a> {
    LessThan(Box<Expr<'a>>, Box<Expr<'a>>),
    LessThanEq(Box<Expr<'a>>, Box<Expr<'a>>),
    GreaterThan(Box<Expr<'a>>, Box<Expr<'a>>),
    GreaterThanEq(Box<Expr<'a>>, Box<Expr<'a>>),
    Eq(Box<Expr<'a>>, Box<Expr<'a>>),
    NotEq(Box<Expr<'a>>, Box<Expr<'a>>),
}

pub enum Expr<'a> {
    Multiply(Box<Expr<'a>>, Box<Expr<'a>>),
    Add(Box<Expr<'a>>, Box<Expr<'a>>),
    Subtract(Box<Expr<'a>>, Box<Expr<'a>>),
    Divide(Box<Expr<'a>>, Box<Expr<'a>>),
    Inverse(Box<Expr<'a>>),
    Proposition(&'a str),
    Weight(i32),
}

pub struct Declaration<'a> {
    pub name: &'a str,
    pub formula: Formula<'a>,
}

#[cfg(test)]
mod tests {
    use std::{fs, path::Path};

    use super::*;
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

        let bad = [];

        assert_good!(good, parser);
        assert_bad!(bad, parser);
    }
}
