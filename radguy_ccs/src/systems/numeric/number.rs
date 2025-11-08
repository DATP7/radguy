use std::{
    cmp::Ordering,
    fmt::Display,
    ops::{Add, Div, Mul, Sub},
};

use radguy::Bottom;

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum Number {
    Val(u32),
    Inf,
}

impl PartialOrd for Number {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Number::Val(l), Number::Val(r)) => l.partial_cmp(r),
            (Number::Val(_), Number::Inf) => Some(Ordering::Less),
            (Number::Inf, Number::Val(_)) => Some(Ordering::Greater),
            (Number::Inf, Number::Inf) => Some(Ordering::Equal),
        }
    }
}

impl Ord for Number {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other)
            .expect("All ordering cases should have been covered by PartialOrd")
    }
}

impl Add for Number {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Val(l), Number::Val(r)) => Number::Val(l + r),
            _ => Number::Inf,
        }
    }
}

impl Mul for Number {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Val(l), Number::Val(r)) => Number::Val(l * r),
            _ => Number::Inf,
        }
    }
}

impl Div for Number {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Val(l), Number::Val(r)) => Number::Val(l / r),
            _ => Number::Inf,
        }
    }
}

impl Sub for Number {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Number::Val(l), Number::Val(r)) => Number::Val(l - r),
            _ => Number::Inf,
        }
    }
}

impl Bottom for Number {
    fn bottom() -> Self {
        Number::Val(0)
    }
}

impl Display for Number {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Number::Val(num) => write!(f, "{num}"),
            Number::Inf => write!(f, "inf"),
        }
    }
}
