use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
};

use itertools::iproduct;
use radguy::{
    Arguments, Assignment, PairUniverse, System, Universe,
    extension::TermSystem,
    ordered::strategy::{InitialStrategy, StrategyHeap, StrategyItem},
};
use radguy::{Union, bislotmap::BiSlotMap};
use slotmap::{Key, SecondaryMap};

pub mod extension;

pub trait BoolSystem<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone>:
    TermSystem<V, bool, T>
{
    fn get_term(&self, term_key: T) -> BoolTerm<V, T>;
    fn evaluate_term(&self, term_key: T, assignment: &dyn Assignment<V, bool>) -> bool;
}

#[derive(Default, Debug)]
pub struct BoolSystemImpl<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone> {
    pub names: BiSlotMap<V, N>,
    pub definitions: SecondaryMap<V, T>,
    pub terms: BiSlotMap<T, BoolTerm<V, T>>,
    term_arguments_cache: RefCell<HashMap<T, HashSet<V>>>,
}

impl<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone> BoolSystemImpl<V, T, N> {
    pub fn term_arguments(&self, term_key: T) -> HashSet<V> {
        if let Some(cached) = self.term_arguments_cache.borrow().get(&term_key) {
            return cached.clone();
        }
        let args = match self.terms.get_value(term_key) {
            BoolTerm::False | BoolTerm::True => HashSet::new(),
            BoolTerm::Variable(k) => {
                let mut set = HashSet::new();
                set.insert(*k);
                set
            }
            BoolTerm::Or(lhs, rhs) | BoolTerm::And(lhs, rhs) => {
                self.term_arguments(*lhs).union(self.term_arguments(*rhs))
            }
        };
        let insert = self
            .term_arguments_cache
            .borrow_mut()
            .insert(term_key, args.clone());
        debug_assert!(insert.is_none(), "term should not already be cached");
        args
    }
}

impl<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone + Debug> BoolSystemImpl<V, T, N> {
    pub fn print_assignment(&self, a: &dyn Assignment<V, bool>) {
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

impl<K: Key, T: Key, N: Hash + Eq + Clone> Universe<HashSet<K>> for BoolSystemImpl<K, T, N> {
    fn universe(&self) -> HashSet<K> {
        self.definitions.keys().collect()
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone> PairUniverse<HashSet<(K, K)>>
    for BoolSystemImpl<K, T, N>
{
    fn pair_universe(&self) -> HashSet<(K, K)> {
        iproduct!(self.names.keys(), self.names.keys()).collect()
    }
}
impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone> System<VarKey, bool>
    for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn evaluate(&self, key: VarKey, assignment: &dyn Assignment<VarKey, bool>) -> bool {
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.evaluate_term(*term_key, assignment)
    }

    fn bottom_assignment(&self) -> impl Assignment<VarKey, bool> {
        HashMap::new()
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone>
    TermSystem<VarKey, bool, TermKey> for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn definition(&self, variable: VarKey) -> TermKey {
        *self
            .definitions
            .get(variable)
            .expect("variable should have a definition")
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone>
    Arguments<VarKey, HashSet<VarKey>> for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn arguments(&self, key: VarKey) -> HashSet<VarKey> {
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.term_arguments(*term_key)
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone>
    BoolSystem<VarKey, TermKey, VarName> for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn get_term(&self, term_key: TermKey) -> BoolTerm<VarKey, TermKey> {
        self.terms.get_value(term_key).clone()
    }

    fn evaluate_term(&self, term_key: TermKey, assignment: &dyn Assignment<VarKey, bool>) -> bool {
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
}

impl<VarKey: Key + Hash + Clone, TermKey: Key + Hash, VarName: Hash + Eq + Clone>
    InitialStrategy<VarKey, bool, StrategyHeap<(VarKey, VarKey)>>
    for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn get_initial_strategy(&self) -> StrategyHeap<(VarKey, VarKey)> {
        iproduct!(self.names.keys(), self.names.keys())
            .map(|(x, y)| StrategyItem::infinite((x, y)).reversed())
            .collect()
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
        sys: &BoolSystemImpl<V, T, N>,
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

    pub fn to_string<N: Hash + Clone + Eq + Display>(
        &self,
        sys: &BoolSystemImpl<V, T, N>,
    ) -> String {
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
        let lhs = $crate::bool_term!($lhs; $system);
        let rhs = $crate::bool_term!($rhs; $system);
        $system.terms.get_or_insert_key($crate::systems::bool::BoolTerm::Or(lhs, rhs))
        }};
    (($lhs:tt && $rhs:tt); $system:expr) => {{
        let lhs = $crate::bool_term!($lhs; $system);
        let rhs = $crate::bool_term!($rhs; $system);
        $system.terms.get_or_insert_key($crate::systems::bool::BoolTerm::And(lhs, rhs))
    }};
}

#[macro_export]
macro_rules! bool_def {
    ($id:ident = $def:tt; $system:expr) => {{
        {let term = $crate::bool_term!($def; $system);
        let key = $system.names.get_or_insert_key(stringify!($id));
        $system.definitions.insert(key, term);
        }
    }};
}

#[macro_export]
macro_rules! bool_system {
    ($($id:ident = $def:tt;)*) => {
        {
            let mut system = $crate::systems::bool::BoolSystemImpl::<slotmap::DefaultKey, slotmap::DefaultKey, &str>::default();
            $(
                $crate::bool_def!($id = $def; system);
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
