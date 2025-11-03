use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
};

use itertools::iproduct;
use radguy::{
    Arguments, Assignment, PairUniverse, Set, System, Universe, bdd::SimpleBDDSet,
    extension::TermSystem,
};
use radguy::{Union, bislotmap::BiSlotMap};
use slotmap::{Key, SecondaryMap};

pub mod extension;

#[derive(Default, Debug)]
pub struct BoolSystem<K: Key, T: Key, N: Hash + Eq + Clone> {
    pub names: BiSlotMap<K, N>,
    pub definitions: SecondaryMap<K, T>,
    pub terms: BiSlotMap<T, BoolTerm<K, T>>,
}

impl<K: Key, T: Key, N: Hash + Eq + Clone> BoolSystem<K, T, N> {
    pub fn evaluate_term(&self, term_key: T, assignment: &dyn Assignment<K, bool>) -> bool {
        match self.terms.get_value(term_key) {
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

    pub fn term_arguments<ArgSet: Set<K> + Union + Default>(&self, term_key: T) -> ArgSet {
        match self.terms.get_value(term_key) {
            BoolTerm::False | BoolTerm::True => ArgSet::default(),
            BoolTerm::Variable(k) => {
                let mut set = ArgSet::default();
                set.insert(*k);
                set
            }
            BoolTerm::Or(lhs, rhs) | BoolTerm::And(lhs, rhs) => self
                .term_arguments::<ArgSet>(*lhs)
                .union(self.term_arguments(*rhs)),
        }
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone + Debug> BoolSystem<K, T, N> {
    pub fn print_assignment(&self, a: &dyn Assignment<K, bool>) {
        for (key, name) in self.names.iter() {
            println!("{name:?} = {:?}", a.get(&key));
        }
    }

    pub fn print_definitions(&self) {
        for (var, term) in &self.definitions {
            println!(
                "{:?} = {:?}",
                self.names.get_value(var),
                self.terms.get_value(*term).to_string_debug(self)
            );
        }
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone> Universe<HashSet<K>> for BoolSystem<K, T, N> {
    fn universe(&self) -> HashSet<K> {
        self.definitions.keys().collect()
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone> PairUniverse<HashSet<(K, K)>> for BoolSystem<K, T, N> {
    fn pair_universe(&self) -> HashSet<(K, K)> {
        iproduct!(self.names.keys(), self.names.keys()).collect()
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone> Universe<SimpleBDDSet> for BoolSystem<K, T, N> {
    fn universe(&self) -> SimpleBDDSet {
        SimpleBDDSet::t()
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone> PairUniverse<SimpleBDDSet> for BoolSystem<K, T, N> {
    fn pair_universe(&self) -> SimpleBDDSet {
        SimpleBDDSet::t()
    }
}

impl<VarKey: Key, TermKey: Key, VarName: Hash + Eq + Clone> System<VarKey, bool>
    for BoolSystem<VarKey, TermKey, VarName>
{
    fn evaluate(&self, key: VarKey, assignment: &dyn Assignment<VarKey, bool>) -> bool {
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.evaluate_term(*term_key, assignment)
    }

    fn bottom_assignment(&self) -> impl Assignment<VarKey, bool> {
        HashMap::new()
    }
}

impl<VarKey: Key, TermKey: Key, VarName: Hash + Eq + Clone> Arguments<VarKey, HashSet<VarKey>>
    for BoolSystem<VarKey, TermKey, VarName>
{
    fn arguments(&self, key: VarKey) -> HashSet<VarKey> {
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.term_arguments(*term_key)
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone>
    TermSystem<VarKey, bool, TermKey> for BoolSystem<VarKey, TermKey, VarName>
{
    fn definition(&self, variable: VarKey) -> TermKey {
        *self
            .definitions
            .get(variable)
            .expect("variable should have a definition")
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum BoolTerm<V: Key, T: Key> {
    True,
    False,
    Variable(V),
    Or(T, T),
    And(T, T),
}

impl<V: Key, T: Key> BoolTerm<V, T> {
    pub fn to_string_debug<N: Hash + Clone + Eq + Debug>(
        &self,
        sys: &BoolSystem<V, T, N>,
    ) -> String {
        match self {
            Self::True => "tt".to_owned(),
            Self::False => "ff".to_owned(),
            Self::Variable(k) => format!("{:?}", *sys.names.get_value(*k)),
            Self::Or(lhs, rhs) => format!(
                "({} || {})",
                sys.terms.get_value(*lhs).to_string_debug(sys),
                sys.terms.get_value(*rhs).to_string_debug(sys)
            ),
            Self::And(lhs, rhs) => format!(
                "({} && {})",
                sys.terms.get_value(*lhs).to_string_debug(sys),
                sys.terms.get_value(*rhs).to_string_debug(sys)
            ),
        }
    }

    pub fn to_string<N: Hash + Clone + Eq + Display>(&self, sys: &BoolSystem<V, T, N>) -> String {
        match self {
            Self::True => "tt".to_owned(),
            Self::False => "ff".to_owned(),
            Self::Variable(k) => format!("{}", *sys.names.get_value(*k)),
            Self::Or(lhs, rhs) => format!(
                "({} || {})",
                sys.terms.get_value(*lhs).to_string(sys),
                sys.terms.get_value(*rhs).to_string(sys)
            ),
            Self::And(lhs, rhs) => format!(
                "({} && {})",
                sys.terms.get_value(*lhs).to_string(sys),
                sys.terms.get_value(*rhs).to_string(sys)
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
            let mut system = $crate::systems::bool::BoolSystem::<slotmap::DefaultKey, slotmap::DefaultKey, &str>::default();
            $(
                bool_def!($id = $def; system);
            )*
            system
        }
    };
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_bool_system_and_or() {
        let sys = bool_system! {
            x = (z || y);
            z = (k && b);
            y = ((z || x) && (k && a));
            k = tt;
            b = a;
            a = tt;
            h = (((z || x) && k) && a);
        };
        for (key, term) in &sys.definitions {
            let var = *sys.names.get_value(key);
            match var {
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "(z || y)"),
                "z" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "(k && b)"),
                "y" => assert_eq!(
                    sys.terms.get_value(*term).to_string(&sys),
                    "((z || x) && (k && a))"
                ),
                "k" | "a" => {
                    assert_eq!(sys.terms.get_value(*term).to_string(&sys), "tt");
                }
                "b" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "a"),
                "h" => assert_eq!(
                    sys.terms.get_value(*term).to_string(&sys),
                    "(((z || x) && k) && a)"
                ),
                &_ => panic!("{var} not found"),
            }
        }
    }

    #[test]
    fn test_bool_system_variables() {
        let sys = bool_system! {
            x = z;
            z = y;
            y = tt;
        };
        for (key, term) in &sys.definitions {
            let var = *sys.names.get_value(key);
            match var {
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "z"),
                "z" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "y"),
                "y" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "tt"),
                &_ => panic!("{var} not found"),
            }
        }
    }

    #[test]
    fn test_bool_system_tt_ff() {
        let sys = bool_system! {
            x = tt;
            y = ff;
            z = tt;
        };
        for (key, term) in &sys.definitions {
            let var = *sys.names.get_value(key);
            match var {
                "x" | "z" => {
                    assert_eq!(sys.terms.get_value(*term).to_string(&sys), "tt");
                }
                "y" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "ff"),
                &_ => panic!("{var} not found"),
            }
        }
    }
}
