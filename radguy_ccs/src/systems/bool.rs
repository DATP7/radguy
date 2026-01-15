use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
};

use itertools::{Itertools, iproduct};
use radguy::{
    Arguments, Assignment, Cartesian, Intersect, PairUniverse, Set, System, Universe, Visited,
    arena::{BiArena, Key, SecondaryArena},
    extension::TermSystem,
    set::bitset::{BitSet, BitsetRelation},
};

pub mod extension;
pub mod strategic_extension;

pub trait BoolSystem<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone>:
    TermSystem<V, bool, T>
{
    fn get_term(&self, term_key: T) -> BoolTerm<V, T>;
    fn evaluate_term(&self, term_key: T, assignment: &dyn Assignment<V, bool>) -> bool;
}

#[derive(Default, Debug, Clone)]
pub struct BoolSystemImpl<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone> {
    pub names: BiArena<V, N>,
    pub definitions: SecondaryArena<V, T>,
    pub terms: BiArena<T, BoolTerm<V, T>>,
    term_arguments_cache: RefCell<HashMap<T, BitSet<V>>>,
    target: Option<V>,
}

impl<V: Key, T: Key + Hash, N: Hash + Eq + Clone> BoolSystemImpl<V, T, N> {
    pub fn term_arguments(&self, term_key: T) -> BitSet<V> {
        if let Some(cached) = self.term_arguments_cache.borrow().get(&term_key) {
            return cached.clone();
        }
        let args = match self.terms.get_value(term_key) {
            BoolTerm::False | BoolTerm::True => BitSet::new(),
            BoolTerm::Variable(k) => BitSet::from([*k]),
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

    pub const fn set_target(&mut self, target: V) {
        self.target = Some(target);
    }
}

impl<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone + Debug> BoolSystemImpl<V, T, N> {
    pub fn print_assignment(&self, a: &dyn Assignment<V, bool>) {
        for (key, name) in &self.names {
            println!("{name:?} = {:?}", a.get_assignment(&key));
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
        self.names.keys().collect()
    }
}
impl<K: Key, T: Key, N: Hash + Eq + Clone> Universe<BitSet<K>> for BoolSystemImpl<K, T, N> {
    fn universe(&self) -> BitSet<K> {
        BitSet::full(self.names.len())
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone> PairUniverse<HashSet<(K, K)>>
    for BoolSystemImpl<K, T, N>
{
    fn pair_universe(&self) -> HashSet<(K, K)> {
        iproduct!(self.names.keys(), self.names.keys(),).collect()
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone> PairUniverse<BitsetRelation<K, K>>
    for BoolSystemImpl<K, T, N>
{
    fn pair_universe(&self) -> BitsetRelation<K, K> {
        // PERF: we might be able to build this relation faster when we know that it will be full
        let universe: BitSet<_> = self.universe();
        universe.cartesian(&universe)
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    System<VarKey, bool> for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn evaluate(&self, key: VarKey, assignment: &HashMap<VarKey, bool>) -> bool {
        let term_key = self
            .definitions
            .get(key)
            .unwrap_or_else(|| panic!("variable {:?} must be defined", self.names.get_value(key)));
        self.evaluate_term(*term_key, assignment)
    }

    fn bottom_assignment(&self) -> HashMap<VarKey, bool> {
        HashMap::new()
    }

    fn lock(&mut self) {
        // Nothing to do
    }

    fn unlock(&mut self) {
        // Nothing to do
    }

    fn target(&self) -> Option<VarKey> {
        self.target
    }
}

impl<
    VarKey: Key + Hash,
    TermKey: Key + Hash,
    VarName: Hash + Eq + Clone + Debug,
    S: FromIterator<VarKey>,
> Visited<S> for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn visited(&self) -> S {
        self.definitions.keys().collect()
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    TermSystem<VarKey, bool, TermKey> for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn definition(&self, variable: VarKey) -> TermKey {
        *self
            .definitions
            .get(variable)
            .expect("variable should have a definition")
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    Arguments<VarKey, HashSet<VarKey>> for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn arguments(&self, key: VarKey) -> HashSet<VarKey> {
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.term_arguments(*term_key).into_iter().collect()
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    Arguments<VarKey, BitSet<VarKey>> for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn arguments(&self, key: VarKey) -> BitSet<VarKey> {
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.term_arguments(*term_key).into_iter().collect()
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    BoolSystem<VarKey, TermKey, VarName> for BoolSystemImpl<VarKey, TermKey, VarName>
{
    fn get_term(&self, term_key: TermKey) -> BoolTerm<VarKey, TermKey> {
        self.terms.get_value(term_key).clone()
    }

    fn evaluate_term(&self, term_key: TermKey, assignment: &dyn Assignment<VarKey, bool>) -> bool {
        match self.terms.get_value(term_key) {
            BoolTerm::True => true,
            BoolTerm::False => false,
            BoolTerm::Variable(k) => assignment.get_assignment(k),
            BoolTerm::Or(term_keys) => term_keys
                .iter()
                .any(|term_key| self.evaluate_term(*term_key, assignment)),
            BoolTerm::And(term_keys) => term_keys
                .iter()
                .all(|term_key| self.evaluate_term(*term_key, assignment)),
        }
    }
}

/// Lazy bool system which ensures variables are not expanded when locked.
/// Intended for testing local oracles.
/// Not for production use.
#[derive(Default, Debug)]
pub struct LazyBoolSystem<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone> {
    pub inner: RefCell<BoolSystemImpl<V, T, N>>,
    visited: RefCell<HashSet<V>>,
    discovered: RefCell<HashSet<V>>,
    locked: bool,
}

impl<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone> From<BoolSystemImpl<V, T, N>>
    for LazyBoolSystem<V, T, N>
{
    fn from(global_system: BoolSystemImpl<V, T, N>) -> Self {
        Self {
            inner: RefCell::new(global_system),
            visited: RefCell::new(HashSet::new()),
            discovered: RefCell::new(HashSet::new()),
            locked: false,
        }
    }
}

macro_rules! ensure_lazy_access {
    ($self:expr, $key:ident) => {
        debug_assert!(!$self.locked || $self.visited.borrow().contains(&$key));
        if (!$self.locked) {
            $self.visited.borrow_mut().insert($key);
            let args: HashSet<_> = $self.inner.borrow().arguments($key);
            $self.discovered.borrow_mut().extend(args.into_iter());
        }
    };
}

impl<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone + Debug> LazyBoolSystem<V, T, N> {
    pub fn init_target(&mut self, target: N) -> V {
        self.visited.replace(HashSet::new());
        self.discovered.replace(HashSet::new());
        let key = self.inner.borrow_mut().names.get_or_insert_key(target);
        self.inner.borrow_mut().set_target(key);
        self.discovered.borrow_mut().insert(key);
        key
    }

    pub fn print_assignment(&self, a: &dyn Assignment<V, bool>) {
        self.inner.borrow().print_assignment(a);
    }

    pub fn print_definitions(&self) {
        self.inner.borrow().print_definitions();
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone, S: Set<K> + Intersect<HashSet<K>> + Debug> Universe<S>
    for LazyBoolSystem<K, T, N>
where
    BoolSystemImpl<K, T, N>: Universe<S>,
{
    fn universe(&self) -> S {
        self.inner
            .borrow()
            .universe()
            .intersect(&self.discovered.borrow())
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone, PS: Set<(K, K)> + FromIterator<(K, K)>> PairUniverse<PS>
    for LazyBoolSystem<K, T, N>
{
    fn pair_universe(&self) -> PS {
        self.discovered
            .borrow()
            .cartesian(&*self.discovered.borrow())
            .into_iter()
            .collect()
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    System<VarKey, bool> for LazyBoolSystem<VarKey, TermKey, VarName>
{
    fn evaluate(&self, key: VarKey, assignment: &HashMap<VarKey, bool>) -> bool {
        ensure_lazy_access!(self, key);
        self.inner.borrow().evaluate(key, assignment)
    }

    fn bottom_assignment(&self) -> HashMap<VarKey, bool> {
        HashMap::new()
    }

    fn lock(&mut self) {
        self.inner.borrow_mut().lock();
    }

    fn unlock(&mut self) {
        self.inner.borrow_mut().unlock();
    }

    fn target(&self) -> Option<VarKey> {
        self.inner.borrow().target()
    }
}

impl<
    VarKey: Key + Hash,
    TermKey: Key + Hash,
    VarName: Hash + Eq + Clone + Debug,
    S: Set<VarKey> + FromIterator<VarKey>,
> Visited<S> for LazyBoolSystem<VarKey, TermKey, VarName>
{
    fn visited(&self) -> S {
        self.visited.borrow().iter().copied().collect()
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    TermSystem<VarKey, bool, TermKey> for LazyBoolSystem<VarKey, TermKey, VarName>
{
    fn definition(&self, variable: VarKey) -> TermKey {
        ensure_lazy_access!(self, variable);
        self.inner.borrow().definition(variable)
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug, VarSet>
    Arguments<VarKey, VarSet> for LazyBoolSystem<VarKey, TermKey, VarName>
where
    BoolSystemImpl<VarKey, TermKey, VarName>:
        Arguments<VarKey, VarSet> + Arguments<VarKey, HashSet<VarKey>>,
{
    fn arguments(&self, key: VarKey) -> VarSet {
        ensure_lazy_access!(self, key);
        self.inner.borrow().arguments(key)
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    BoolSystem<VarKey, TermKey, VarName> for LazyBoolSystem<VarKey, TermKey, VarName>
{
    fn get_term(&self, term_key: TermKey) -> BoolTerm<VarKey, TermKey> {
        self.inner.borrow().get_term(term_key)
    }

    fn evaluate_term(&self, term_key: TermKey, assignment: &dyn Assignment<VarKey, bool>) -> bool {
        self.inner.borrow().evaluate_term(term_key, assignment)
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
                    .sorted()
                    .join(", "),
            ),
            Self::And(elements) => format!(
                "and({})",
                elements
                    .iter()
                    .map(|term_key| sys.terms.get_value(*term_key).to_string(sys))
                    .sorted()
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
    (($lhs:tt $(|| $rest:tt)+); $system:expr) => {{
        let mut terms = Vec::from([$($crate::bool_term!($rest; $system),)+]);
        terms.push($crate::bool_term!($lhs; $system));
        $system.terms.get_or_insert_key($crate::systems::bool::BoolTerm::Or(terms))
        }};
    (($lhs:tt $(&& $rest:tt)+); $system:expr) => {{
        let mut terms = Vec::from([$($crate::bool_term!($rest; $system),)+]);
        terms.push($crate::bool_term!($lhs; $system));
        $system.terms.get_or_insert_key($crate::systems::bool::BoolTerm::And(terms))
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
            let mut system = $crate::systems::bool::BoolSystemImpl::<usize, usize, &str>::default();
            $(
                $crate::bool_def!($id = $def; system);
            )*
            system
        }
    };
}

#[macro_export]
macro_rules! lazy_bool_system {
    ($($id:ident = $def:tt;)*) => {
        {
            let mut system = $crate::systems::bool::LazyBoolSystem::<usize, usize, &str>::default();
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

    use radguy::{Arguments, System, set::bitset::BitSet};

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
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "or(y, z)"),
                "z" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "and(b, k)"),
                "y" => assert_eq!(
                    sys.terms.get_value(*term).to_string(&sys),
                    "and(and(a, k), or(x, z))"
                ),
                "k" | "a" => {
                    assert_eq!(sys.terms.get_value(*term).to_string(&sys), "tt");
                }
                "b" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "a"),
                "h" => assert_eq!(
                    sys.terms.get_value(*term).to_string(&sys),
                    "and(a, and(k, or(x, z)))"
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
    fn bool_system_chain_and_or() {
        let sys = bool_system! {
            x = (x && y && z);
            y = (x || y || z);
            z = ((x && y && z) || (x && y) || (y || z));
        };
        for (key, term) in &sys.definitions {
            let var = *sys.names.get_value(key);
            match var {
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "and(x, y, z)"),
                "y" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "or(x, y, z)"),
                "z" => assert_eq!(
                    sys.terms.get_value(*term).to_string(&sys),
                    "or(and(x, y), and(x, y, z), or(y, z))"
                ),
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

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn arguments() {
        let mut sys = bool_system! {
            x = (x || y || z);
            y = (u && y && z);
            z = (x && (y || v));
            u = tt;
            v = ff;
        };
        let x = sys.names.get_or_insert_key("x");
        let y = sys.names.get_or_insert_key("y");
        let z = sys.names.get_or_insert_key("z");
        let u = sys.names.get_or_insert_key("u");
        let v = sys.names.get_or_insert_key("v");

        assert_eq!(BitSet::from([x, y, z]), sys.arguments(x));
        assert_eq!(BitSet::from([u, y, z]), sys.arguments(y));
        assert_eq!(BitSet::from([x, y, v]), sys.arguments(z));
        assert_eq!(BitSet::new(), sys.arguments(u));
        assert_eq!(BitSet::new(), sys.arguments(v));
    }
}
