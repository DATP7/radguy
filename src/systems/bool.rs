use std::hash::Hash;

use crate::bislotmap::BiSlotMap;
use slotmap::{Key, SecondaryMap};

#[derive(Default, Debug)]
pub struct BoolSystem<V: Key + Hash, T: Key + Hash> {
    // TODO: This lifetime needs to be better than 'static
    pub names: BiSlotMap<V, &'static str>,
    pub definitions: SecondaryMap<V, T>,
    pub terms: BiSlotMap<T, BoolTerm<V, T>>,
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum BoolTerm<V: Key, T: Key> {
    True,
    False,
    Variable(V),
    Or(T, T),
    And(T, T),
}

#[macro_export]
macro_rules! bool_term {
    (tt; $system:expr) => {
        $system.terms.get_or_insert_key($crate::systems::bool::BoolTerm::True)
    };
    (ff; $system:expr) => {
        $system.terms.get_or_insert_key($crate::systems::bool::BoolTerm::False)
    };
    ($id:ident; $system:expr) => {{
            let var_key = $system.names.get_or_insert_key(stringify!($id));
            $system.terms.get_or_insert_key($crate::systems::bool::BoolTerm::Variable(var_key))
    }};
    (($lhs:tt || $rhs:tt); $system:expr) => {{
        let lhs = bool_term!($lhs; $system);
        let rhs = bool_term!($rhs; $system);
        $system.terms.get_or_insert_key($crate::systems::bool::BoolTerm::Or(lhs, rhs))
        }};
    (($lhs:tt && $rhs:tt); $system:expr) => {{
        let lhs = bool_term!($lhs; $system);
        let rhs = bool_term!($rhs; $system);
        $system.terms.get_or_insert_key($crate::systems::bool::BoolTerm::And(lhs, rhs))
    }};
}

#[macro_export]
macro_rules! bool_def {
    ($id:ident = $def:tt; $system:expr) => {{
        {let term = bool_term!($def; $system);
        let key = $system.names.get_or_insert_key(stringify!($id));
        $system.definitions.insert(key, term);
        }
    }};
}

#[macro_export]
macro_rules! bool_system {
    ($($id:ident = $def:tt;)*) => {
        {
            let mut system = $crate::systems::bool::BoolSystem::<slotmap::DefaultKey, slotmap::DefaultKey>::default();
            $(
                bool_def!($id = $def; system);
            )*
            system
        }
    };
}
