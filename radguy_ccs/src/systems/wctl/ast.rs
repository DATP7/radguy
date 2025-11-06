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
    Id(&'a str),
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
