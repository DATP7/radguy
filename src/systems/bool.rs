use std::{
    collections::{HashMap, HashSet},
    hash::Hash,
};

use crate::bislotmap::BiSlotMap;
use radguy::{Assignment, System, extension::TermSystem};
use slotmap::{Key, SecondaryMap};

#[derive(Default, Debug)]
pub struct BoolSystem<V: Key + Hash, T: Key + Hash> {
    // TODO: This lifetime needs to be better than 'static
    pub names: BiSlotMap<V, &'static str>,
    pub definitions: SecondaryMap<V, T>,
    pub terms: BiSlotMap<T, BoolTerm<V, T>>,
}

#[allow(warnings)]
impl<V: Key + Hash, T: Key + Hash> BoolSystem<V, T> {
    pub fn print_assignment(&self, a: &dyn Assignment<V, bool>) {
        for (key, &name) in self.names.iter() {
            println!("{name} = {}", a.get(&key));
        }
    }

    pub fn print_definitions(&self) {
        for (var, term) in &self.definitions {
            println!(
                "{} = {}",
                self.names
                    .get_value(var)
                    .expect("variable should have name"),
                self.terms
                    .get_value(*term)
                    .expect("term should be valid")
                    .to_string(self)
            );
        }
    }

    fn evaluate_term(&self, term_key: T, assignment: &dyn Assignment<V, bool>) -> bool {
        match self.terms.get_value(term_key).expect("term must exist") {
            BoolTerm::True => true,
            BoolTerm::False => false,
            BoolTerm::Variable(k) => assignment.get(k),
            BoolTerm::Or(lhs, rhs) => {
                self.evaluate_term(*lhs, assignment) || self.evaluate_term(*rhs, assignment)
            }
            BoolTerm::And(lhs, rhs) => {
                self.evaluate_term(*lhs, assignment) && self.evaluate_term(*rhs, assignment)
            }
        }
    }

    fn term_arguments(&self, term_key: T) -> HashSet<V> {
        match self.terms.get_value(term_key).expect("term must exist") {
            BoolTerm::False | BoolTerm::True => HashSet::new(),
            BoolTerm::Variable(k) => HashSet::from_iter([*k]),
            BoolTerm::Or(lhs, rhs) | BoolTerm::And(lhs, rhs) => self
                .term_arguments(*lhs)
                .union(&self.term_arguments(*rhs))
                .copied()
                .collect(),
        }
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash> System<VarKey, bool> for BoolSystem<VarKey, TermKey> {
    fn evaluate(&self, key: VarKey, assignment: &dyn Assignment<VarKey, bool>) -> bool {
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.evaluate_term(*term_key, assignment)
    }

    fn arguments(&self, key: VarKey) -> HashSet<VarKey> {
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.term_arguments(*term_key)
    }

    fn variables(&self) -> HashSet<VarKey> {
        self.definitions.keys().collect()
    }

    fn bottom_assignment(&self) -> impl Assignment<VarKey, bool> {
        HashMap::new()
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash> TermSystem<VarKey, bool, TermKey>
    for BoolSystem<VarKey, TermKey>
{
    fn definition(&self, variable: VarKey) -> TermKey {
        *self
            .definitions
            .get(variable)
            .expect("variable should have a definition")
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
#[allow(warnings)]
pub enum BoolTerm<V: Key, T: Key> {
    True,
    False,
    Variable(V),
    Or(T, T),
    And(T, T),
}

impl<V: Key, T: Key> BoolTerm<V, T> {
    pub fn to_string(&self, sys: &BoolSystem<V, T>) -> String {
        match self {
            Self::True => "tt".to_owned(),
            Self::False => "ff".to_owned(),
            Self::Variable(k) => {
                (*sys.names.get_value(*k).expect("variable must have name")).to_owned()
            }
            Self::Or(lhs, rhs) => format!(
                "{} || {}",
                sys.terms
                    .get_value(*lhs)
                    .expect("lhs should exist")
                    .to_string(sys),
                sys.terms
                    .get_value(*rhs)
                    .expect("rhs should exist")
                    .to_string(sys)
            ),
            Self::And(lhs, rhs) => format!(
                "{} && {}",
                sys.terms
                    .get_value(*lhs)
                    .expect("lhs should exist")
                    .to_string(sys),
                sys.terms
                    .get_value(*rhs)
                    .expect("rhs should exist")
                    .to_string(sys)
            ),
        }
    }
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
