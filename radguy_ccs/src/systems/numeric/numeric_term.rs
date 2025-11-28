use radguy::arena::Key;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::fmt::Display;
use std::hash::Hash;

use crate::systems::numeric::{number::Number, numeric_system::NumericSystemImpl};

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum NumericTerm<V: Key, T: Key> {
    Const(Number),
    Var(V),
    Add(T, T),
    Mult(T, T),
    Min(BTreeSet<T>),
    Max(BTreeSet<T>),
    Bound { bound: Number, term: T },
}

impl<V: Key, T: Key> NumericTerm<V, T> {
    pub fn to_string_debug<N: Hash + Clone + Eq + Debug>(
        &self,
        sys: &NumericSystemImpl<V, T, N>,
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
            Self::Min(keys) => format!(
                "min({})",
                keys.iter()
                    .map(|key| sys.terms.get_value(*key).to_string_debug(sys))
                    .collect::<Vec<_>>()
                    .join(", "),
            ),
            Self::Max(keys) => format!(
                "max({})",
                keys.iter()
                    .map(|key| sys.terms.get_value(*key).to_string_debug(sys))
                    .collect::<Vec<_>>()
                    .join(", "),
            ),
            Self::Bound { bound, term } => format!(
                "(bound: {bound}, term: {})",
                sys.terms.get_value(*term).to_string_debug(sys)
            ),
        }
    }

    pub fn to_string<N: Hash + Clone + Eq + Display + Debug>(
        &self,
        sys: &NumericSystemImpl<V, T, N>,
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
            Self::Min(keys) => format!(
                "min({})",
                keys.iter()
                    .map(|key| sys.terms.get_value(*key).to_string(sys))
                    .collect::<Vec<_>>()
                    .join(", "),
            ),
            Self::Max(keys) => format!(
                "max({})",
                keys.iter()
                    .map(|key| sys.terms.get_value(*key).to_string(sys))
                    .collect::<Vec<_>>()
                    .join(", "),
            ),
            Self::Bound { bound, term } => format!(
                "(bound: {bound}, term: {})",
                sys.terms.get_value(*term).to_string(sys)
            ),
        }
    }
}
