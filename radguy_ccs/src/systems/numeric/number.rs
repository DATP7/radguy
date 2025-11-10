use std::{
    cmp::Ordering,
    fmt::Display,
    ops::{Add, Div, Mul, Sub},
};

use radguy::{Bottom, Maximal};

#[derive(Hash, PartialEq, Eq, Clone, Debug, Copy)]
pub enum Number {
    Val(u32),
    Inf,
}

impl PartialOrd for Number {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Number {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Self::Val(l), Self::Val(r)) => l.cmp(r),
            (Self::Val(_), Self::Inf) => Ordering::Less,
            (Self::Inf, Self::Val(_)) => Ordering::Greater,
            (Self::Inf, Self::Inf) => Ordering::Equal,
        }
    }
}

impl Maximal for Number {
    fn is_maximal(&self) -> bool {
        *self == Self::Val(0)
    }
}

impl Add for Number {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Val(l), Self::Val(r)) => Self::Val(l + r),
            _ => Self::Inf,
        }
    }
}

impl Mul for Number {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Val(l), Self::Val(r)) => Self::Val(l * r),
            _ => Self::Inf,
        }
    }
}

impl Div for Number {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Val(l), Self::Val(r)) => Self::Val(l / r),
            _ => Self::Inf,
        }
    }
}

impl Sub for Number {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Self::Val(l), Self::Val(r)) => Self::Val(l - r),
            _ => Self::Inf,
        }
    }
}

impl Bottom for Number {
    fn bottom() -> Self {
        Self::Inf
    }
}

impl Display for Number {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Val(num) => write!(f, "{num}"),
            Self::Inf => write!(f, "inf"),
        }
    }
}
