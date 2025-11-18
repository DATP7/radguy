use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
};

use itertools::{Itertools, iproduct};
use radguy::bislotmap::BiSlotMap;
use radguy::{
    Arguments, Assignment, PairUniverse, System, Universe,
    extension::TermSystem,
    ordered::strategy::{InitialStrategy, Strategy, StrategyItem},
};
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
            BoolTerm::Or(elements) | BoolTerm::And(elements) => elements
                .iter()
                .flat_map(|term_key| self.term_arguments(*term_key))
                .collect(),
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
            BoolTerm::Or(term_keys) => term_keys
                .iter()
                .any(|term_key| self.evaluate_term(*term_key, assignment)),
            BoolTerm::And(term_keys) => term_keys
                .iter()
                .all(|term_key| self.evaluate_term(*term_key, assignment)),
        }
    }
}

impl<
    VarKey: Key + Hash + Clone,
    TermKey: Key + Hash,
    VarName: Hash + Eq + Clone,
    PS: Strategy<(VarKey, VarKey)> + FromIterator<StrategyItem<(VarKey, VarKey)>>,
> InitialStrategy<VarKey, bool, PS> for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn get_initial_strategy(&self) -> PS {
        iproduct!(self.names.keys(), self.names.keys())
            .map(|(x, y)| StrategyItem::infinite((x, y)))
            .collect()
    }
}

#[derive(Hash, PartialEq, Eq, Clone, Debug)]
pub enum BoolTerm<V: Key, T: Key> {
    True,
    False,
    Variable(V),
    Or(Vec<T>),
    And(Vec<T>),
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
            Self::Or(elements) => format!(
                "or({})",
                elements
                    .iter()
                    .map(|term_key| sys.terms.get_value(*term_key).to_string_debug(sys))
                    .join(", "),
            ),
            Self::And(elements) => format!(
                "and({})",
                elements
                    .iter()
                    .map(|term_key| sys.terms.get_value(*term_key).to_string_debug(sys))
                    .join(", "),
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
            Self::Or(elements) => format!(
                "or({})",
                elements
                    .iter()
                    .map(|term_key| sys.terms.get_value(*term_key).to_string(sys))
                    .join(", "),
            ),
            Self::And(elements) => format!(
                "and({})",
                elements
                    .iter()
                    .map(|term_key| sys.terms.get_value(*term_key).to_string(sys))
                    .join(", "),
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
        $system.terms.get_or_insert_key($crate::systems::bool::BoolTerm::Or(Vec::from([lhs, rhs])))
        }};
    (($lhs:tt && $rhs:tt); $system:expr) => {{
        let lhs = $crate::bool_term!($lhs; $system);
        let rhs = $crate::bool_term!($rhs; $system);
        $system.terms.get_or_insert_key($crate::systems::bool::BoolTerm::And(Vec::from([lhs, rhs])))
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
    use std::collections::HashMap;

    use radguy::System;

    #[test]
    fn bool_system_and_or() {
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
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "or(z, y)"),
                "z" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "and(k, b)"),
                "y" => assert_eq!(
                    sys.terms.get_value(*term).to_string(&sys),
                    "and(or(z, x), and(k, a))"
                ),
                "k" | "a" => {
                    assert_eq!(sys.terms.get_value(*term).to_string(&sys), "tt");
                }
                "b" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "a"),
                "h" => assert_eq!(
                    sys.terms.get_value(*term).to_string(&sys),
                    "and(and(or(z, x), k), a)"
                ),
                &_ => panic!("{var} not found"),
            }
        }
    }

    #[test]
    fn bool_system_variables() {
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
    fn bool_system_tt_ff() {
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

    #[test]
    fn bool_system_evaluate_const() {
        let mut sys = bool_system! {
            x = tt;
            y = ff;
        };
        let x = sys.names.get_or_insert_key("x");
        let y = sys.names.get_or_insert_key("y");
        assert!(sys.evaluate(x, &HashMap::new()));
        assert!(!sys.evaluate(y, &HashMap::new()));
    }

    #[test]
    fn bool_system_evaluate_var() {
        let mut sys = bool_system! {
            x = y;
            y = tt;
            z = k;
            k = ff;
        };
        let x = sys.names.get_or_insert_key("x");
        let y = sys.names.get_or_insert_key("y");
        let z = sys.names.get_or_insert_key("z");
        let k = sys.names.get_or_insert_key("k");
        let mut map = HashMap::new();
        map.insert(y, true);
        map.insert(k, false);
        assert!(sys.evaluate(x, &map));
        assert!(!sys.evaluate(z, &map));
    }

    #[test]
    fn bool_system_evaluate_and() {
        let mut sys = bool_system! {
            x = (tt && tt);
            y = (ff && tt);
            z = (tt && ff);
            k = (ff && ff);
        };
        let x = sys.names.get_or_insert_key("x");
        let y = sys.names.get_or_insert_key("y");
        let z = sys.names.get_or_insert_key("z");
        let k = sys.names.get_or_insert_key("k");
        assert!(sys.evaluate(x, &HashMap::new()));
        assert!(!sys.evaluate(y, &HashMap::new()));
        assert!(!sys.evaluate(z, &HashMap::new()));
        assert!(!sys.evaluate(k, &HashMap::new()));
    }

    #[test]
    fn bool_system_evaluate_or() {
        let mut sys = bool_system! {
            x = (tt || tt);
            y = (ff || tt);
            z = (tt || ff);
            k = (ff || ff);
        };
        let x = sys.names.get_or_insert_key("x");
        let y = sys.names.get_or_insert_key("y");
        let z = sys.names.get_or_insert_key("z");
        let k = sys.names.get_or_insert_key("k");
        assert!(sys.evaluate(x, &HashMap::new()));
        assert!(sys.evaluate(y, &HashMap::new()));
        assert!(sys.evaluate(z, &HashMap::new()));
        assert!(!sys.evaluate(k, &HashMap::new()));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn bool_system_evaluate() {
        let mut sys = bool_system! {
            x = (z || y);
            y = (k && a);
            z = ((z || x) && (k && a));
            k = tt;
            b = a;
            a = tt;
            h = (((z || x) && k) && a);
        };
        let x = sys.names.get_or_insert_key("x");
        let y = sys.names.get_or_insert_key("y");
        let z = sys.names.get_or_insert_key("z");
        let k = sys.names.get_or_insert_key("k");
        let b = sys.names.get_or_insert_key("b");
        let a = sys.names.get_or_insert_key("a");
        let h = sys.names.get_or_insert_key("h");
        let mut map = HashMap::new();
        map.insert(x, false);
        map.insert(z, false);
        map.insert(k, true);
        map.insert(b, false);
        map.insert(a, true);
        assert!(!sys.evaluate(x, &map));
        assert!(sys.evaluate(y, &map));
        assert!(!sys.evaluate(z, &map));
        assert!(sys.evaluate(k, &map));
        assert!(sys.evaluate(b, &map));
        assert!(sys.evaluate(a, &map));
        assert!(!sys.evaluate(h, &map));
    }
}
