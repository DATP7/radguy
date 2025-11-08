use slotmap::Key;
use std::fmt::Debug;
use std::fmt::Display;
use std::hash::Hash;

use crate::systems::numeric::{number::Number, numeric_system::NumericSystem};

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum NumericTerm<V: Key, T: Key> {
    Const(Number),
    Var(V),
    Add(T, T),
    Mult(T, T),
    Sub(T, T),
    Div(T, T),
    Min(T, T),
    Max(T, T),
}

impl<V: Key, T: Key> NumericTerm<V, T> {
    pub fn to_string_debug<N: Hash + Clone + Eq + Debug>(
        &self,
        sys: &NumericSystem<V, T, N>,
    ) -> String {
        match self {
            Self::Const(num) => format!("{num}"),
            Self::Var(k) => format!("{:?}", *sys.names.get_value(*k)),
            Self::Add(lhs, rhs) => format!(
                "({} + {})",
                sys.terms.get_value(*lhs).to_string_debug(sys),
                sys.terms.get_value(*rhs).to_string_debug(sys)
            ),
            Self::Mult(lhs, rhs) => format!(
                "({} * {})",
                sys.terms.get_value(*lhs).to_string_debug(sys),
                sys.terms.get_value(*rhs).to_string_debug(sys)
            ),
            Self::Sub(lhs, rhs) => format!(
                "({} - {})",
                sys.terms.get_value(*lhs).to_string_debug(sys),
                sys.terms.get_value(*rhs).to_string_debug(sys)
            ),
            Self::Div(lhs, rhs) => format!(
                "({} / {})",
                sys.terms.get_value(*lhs).to_string_debug(sys),
                sys.terms.get_value(*rhs).to_string_debug(sys)
            ),
            Self::Min(lhs, rhs) => format!(
                "min({}, {})",
                sys.terms.get_value(*lhs).to_string_debug(sys),
                sys.terms.get_value(*rhs).to_string_debug(sys)
            ),
            Self::Max(lhs, rhs) => format!(
                "max({}, {})",
                sys.terms.get_value(*lhs).to_string_debug(sys),
                sys.terms.get_value(*rhs).to_string_debug(sys)
            ),
        }
    }

    pub fn to_string<N: Hash + Clone + Eq + Display>(
        &self,
        sys: &NumericSystem<V, T, N>,
    ) -> String {
        match self {
            Self::Const(num) => format!("{num}"),
            Self::Var(k) => format!("{}", *sys.names.get_value(*k)),
            Self::Add(lhs, rhs) => format!(
                "({} + {})",
                sys.terms.get_value(*lhs).to_string(sys),
                sys.terms.get_value(*rhs).to_string(sys)
            ),
            Self::Mult(lhs, rhs) => format!(
                "({} * {})",
                sys.terms.get_value(*lhs).to_string(sys),
                sys.terms.get_value(*rhs).to_string(sys)
            ),
            Self::Sub(lhs, rhs) => format!(
                "({} - {})",
                sys.terms.get_value(*lhs).to_string(sys),
                sys.terms.get_value(*rhs).to_string(sys)
            ),
            Self::Div(lhs, rhs) => format!(
                "({} / {})",
                sys.terms.get_value(*lhs).to_string(sys),
                sys.terms.get_value(*rhs).to_string(sys)
            ),
            Self::Min(lhs, rhs) => format!(
                "min({}, {})",
                sys.terms.get_value(*lhs).to_string(sys),
                sys.terms.get_value(*rhs).to_string(sys)
            ),
            Self::Max(lhs, rhs) => format!(
                "max({}, {})",
                sys.terms.get_value(*lhs).to_string(sys),
                sys.terms.get_value(*rhs).to_string(sys)
            ),
        }
    }
}
