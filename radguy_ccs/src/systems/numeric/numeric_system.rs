use itertools::iproduct;
use radguy::{
    Arguments, Assignment, Cartesian, Intersect, PairUniverse, Set, System, Union, Universe,
    Visited,
    arena::{BiArena, Key, SecondaryArena},
    extension::TermSystem,
    set::bitset::{BitSet, BitsetRelation},
};
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
};

use crate::systems::numeric::{number::Number, numeric_term::NumericTerm};

pub trait NumericSystem<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone>:
    TermSystem<V, Number, T>
{
    fn get_term(&self, term_key: T) -> NumericTerm<V, T>;
    fn evaluate_term(&self, term_key: T, assignment: &HashMap<V, Number>) -> Number;
}

// This doesn't actually do anything, but is here in case future changes would lead to it being required.
// It is removed in optimized builts anyway
macro_rules! assert_access_allowed {
    ($self:expr, $key:expr) => {
        debug_assert!(
            !$self.locked || $self.definitions.contains_key($key),
            "Variable {:?} was visited for the first time while the system was locked",
            $self.names.get_value($key)
        )
    };
}

#[derive(Default, Debug, Clone)]
pub struct NumericSystemImpl<K: Key, T: Key, N: Hash + Eq + Clone> {
    pub names: BiArena<K, N>,
    pub definitions: SecondaryArena<K, T>,
    pub terms: BiArena<T, NumericTerm<K, T>>,
    locked: bool,
}

impl<K: Key, T: Key, N: Hash + Eq + Clone + Debug> NumericSystem<K, T, N>
    for NumericSystemImpl<K, T, N>
{
    fn get_term(&self, term_key: T) -> NumericTerm<K, T> {
        self.terms.get_value(term_key).clone()
    }

    fn evaluate_term(&self, term_key: T, assignment: &HashMap<K, Number>) -> Number {
        match self.terms.get_value(term_key) {
            NumericTerm::Const(num) => *num,
            NumericTerm::Var(k) => assignment.get_assignment(k),
            NumericTerm::Add(lhs, rhs) => {
                self.evaluate_term(*lhs, assignment) + self.evaluate_term(*rhs, assignment)
            }
            NumericTerm::Mult(lhs, rhs) => {
                self.evaluate_term(*lhs, assignment) * self.evaluate_term(*rhs, assignment)
            }
            NumericTerm::Min(keys) => keys
                .iter()
                .map(|key| self.evaluate_term(*key, assignment))
                .min()
                .unwrap_or(Number::Inf),
            NumericTerm::Max(keys) => keys
                .iter()
                .map(|key| self.evaluate_term(*key, assignment))
                .max()
                .unwrap_or(Number::Val(0)),
            NumericTerm::Bound { bound, term } => {
                let term_val = self.evaluate_term(*term, assignment);
                match bound {
                    Number::Val(_) => {
                        if term_val <= *bound {
                            Number::Val(0)
                        } else {
                            Number::Inf
                        }
                    }
                    Number::Inf => {
                        if term_val < Number::Inf {
                            Number::Val(0)
                        } else {
                            Number::Inf
                        }
                    }
                }
            }
        }
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone + Debug> NumericSystemImpl<K, T, N> {
    pub fn term_arguments<
        ArgSet: Set<K> + Union + Default + FromIterator<K> + IntoIterator<Item = K>,
    >(
        &self,
        term_key: T,
    ) -> ArgSet {
        match self.terms.get_value(term_key) {
            NumericTerm::Const(_) => ArgSet::default(),
            NumericTerm::Var(k) => {
                let mut set = ArgSet::default();
                set.insert(*k);
                set
            }
            NumericTerm::Add(lhs, rhs) | NumericTerm::Mult(lhs, rhs) => self
                .term_arguments::<ArgSet>(*lhs)
                .union(self.term_arguments(*rhs)),
            NumericTerm::Max(keys) | NumericTerm::Min(keys) => keys
                .iter()
                .flat_map(|&key| self.term_arguments::<ArgSet>(key))
                .collect(),
            NumericTerm::Bound { term, .. } => self.term_arguments(*term),
        }
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone + Debug> NumericSystemImpl<K, T, N> {
    pub fn print_assignment(&self, a: &HashMap<K, Number>) {
        for (key, name) in &self.names {
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

impl<K: Key, T: Key, N: Hash + Eq + Clone + Debug> Universe<HashSet<K>>
    for NumericSystemImpl<K, T, N>
{
    fn universe(&self) -> HashSet<K> {
        self.names.keys().collect()
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone + Debug> PairUniverse<HashSet<(K, K)>>
    for NumericSystemImpl<K, T, N>
{
    fn pair_universe(&self) -> HashSet<(K, K)> {
        iproduct!(self.names.keys(), self.names.keys()).collect()
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone + Debug> Universe<BitSet<K>>
    for NumericSystemImpl<K, T, N>
{
    fn universe(&self) -> BitSet<K> {
        self.names.keys().collect()
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone + Debug> PairUniverse<BitsetRelation<K, K>>
    for NumericSystemImpl<K, T, N>
{
    fn pair_universe(&self) -> BitsetRelation<K, K> {
        let u: BitSet<_> = self.universe();
        u.cartesian(&u)
    }
}

impl<VarKey: Key, TermKey: Key, VarName: Hash + Eq + Clone + Debug> System<VarKey, Number>
    for NumericSystemImpl<VarKey, TermKey, VarName>
{
    fn evaluate(&self, key: VarKey, assignment: &HashMap<VarKey, Number>) -> Number {
        assert_access_allowed!(self, key);
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.evaluate_term(*term_key, assignment)
    }

    fn bottom_assignment(&self) -> HashMap<VarKey, Number> {
        HashMap::new()
    }

    fn lock(&mut self) {
        self.locked = true;
    }

    fn unlock(&mut self) {
        self.locked = false;
    }
}

impl<VarKey: Key, TermKey: Key, VarName: Hash + Eq + Clone + Debug, S: FromIterator<VarKey>>
    Visited<S> for NumericSystemImpl<VarKey, TermKey, VarName>
{
    fn visited(&self) -> S {
        self.definitions.keys().collect()
    }
}

impl<VarKey: Key, TermKey: Key, VarName: Hash + Eq + Clone + Debug>
    Arguments<VarKey, HashSet<VarKey>> for NumericSystemImpl<VarKey, TermKey, VarName>
{
    fn arguments(&self, key: VarKey) -> HashSet<VarKey> {
        assert_access_allowed!(self, key);
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.term_arguments(*term_key)
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    TermSystem<VarKey, Number, TermKey> for NumericSystemImpl<VarKey, TermKey, VarName>
{
    fn definition(&self, variable: VarKey) -> TermKey {
        assert_access_allowed!(self, variable);
        *self
            .definitions
            .get(variable)
            .expect("variable should have a definition")
    }
}

/// Lazy numerical system which ensures variables are not expanded when locked.
/// Intended for testing local oracles.
/// Not for production use.
#[derive(Default, Debug)]
pub struct LazyNumericSystem<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone + Debug> {
    pub inner: RefCell<NumericSystemImpl<V, T, N>>,
    visited: RefCell<HashSet<V>>,
    discovered: RefCell<HashSet<V>>,
}

impl<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone + Debug> From<NumericSystemImpl<V, T, N>>
    for LazyNumericSystem<V, T, N>
{
    fn from(global_system: NumericSystemImpl<V, T, N>) -> Self {
        Self {
            inner: RefCell::new(global_system),
            visited: RefCell::new(HashSet::new()),
            discovered: RefCell::new(HashSet::new()),
        }
    }
}

macro_rules! ensure_lazy_access {
    ($self:expr, $key:ident) => {
        debug_assert!(!$self.inner.borrow().locked || $self.visited.borrow().contains(&$key));
        if (!$self.inner.borrow().locked) {
            $self.visited.borrow_mut().insert($key);
            let args = $self.inner.borrow().arguments($key);
            $self.discovered.borrow_mut().extend(args.into_iter());
        }
    };
}

impl<V: Key + Hash, T: Key + Hash, N: Hash + Eq + Clone + Debug> LazyNumericSystem<V, T, N> {
    pub fn init_target(&mut self, target: N) -> V {
        self.visited.replace(HashSet::new());
        self.discovered.replace(HashSet::new());
        let key = self.inner.borrow_mut().names.get_or_insert_key(target);
        self.discovered.borrow_mut().insert(key);
        key
    }

    pub fn print_assignment(&self, a: &HashMap<V, Number>) {
        self.inner.borrow().print_assignment(a);
    }

    pub fn print_definitions(&self) {
        self.inner.borrow().print_definitions();
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone + Debug> Universe<HashSet<K>>
    for LazyNumericSystem<K, T, N>
{
    fn universe(&self) -> HashSet<K> {
        let u: HashSet<_> = self.inner.borrow().universe();
        u.intersect(&self.discovered.borrow())
    }
}

impl<K: Key + Hash + Eq, T: Key, N: Hash + Eq + Clone + Debug> PairUniverse<HashSet<(K, K)>>
    for LazyNumericSystem<K, T, N>
{
    fn pair_universe(&self) -> HashSet<(K, K)> {
        self.discovered
            .borrow()
            .cartesian(&*self.discovered.borrow())
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone + Debug> Universe<BitSet<K>>
    for LazyNumericSystem<K, T, N>
{
    fn universe(&self) -> BitSet<K> {
        let u: BitSet<_> = self.inner.borrow().universe();
        u.intersect(&*self.discovered.borrow())
    }
}

impl<K: Key + Hash + Eq, T: Key, N: Hash + Eq + Clone + Debug> PairUniverse<BitsetRelation<K, K>>
    for LazyNumericSystem<K, T, N>
{
    fn pair_universe(&self) -> BitsetRelation<K, K> {
        let u: BitSet<_> = self.universe();
        u.cartesian(&u)
    }
}
impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    System<VarKey, Number> for LazyNumericSystem<VarKey, TermKey, VarName>
{
    fn evaluate(&self, key: VarKey, assignment: &HashMap<VarKey, Number>) -> Number {
        ensure_lazy_access!(self, key);
        self.inner.borrow().evaluate(key, assignment)
    }

    fn bottom_assignment(&self) -> HashMap<VarKey, Number> {
        HashMap::new()
    }

    fn lock(&mut self) {
        self.inner.borrow_mut().lock();
    }

    fn unlock(&mut self) {
        self.inner.borrow_mut().unlock();
    }
}
impl<VarKey: Key, TermKey: Key, VarName: Hash + Eq + Clone + Debug, S: FromIterator<VarKey>>
    Visited<S> for LazyNumericSystem<VarKey, TermKey, VarName>
{
    fn visited(&self) -> S {
        self.visited.borrow().iter().copied().collect()
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    TermSystem<VarKey, Number, TermKey> for LazyNumericSystem<VarKey, TermKey, VarName>
{
    fn definition(&self, variable: VarKey) -> TermKey {
        ensure_lazy_access!(self, variable);
        self.inner.borrow().definition(variable)
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    Arguments<VarKey, HashSet<VarKey>> for LazyNumericSystem<VarKey, TermKey, VarName>
{
    fn arguments(&self, key: VarKey) -> HashSet<VarKey> {
        ensure_lazy_access!(self, key);
        self.inner.borrow().arguments(key)
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone + Debug>
    NumericSystem<VarKey, TermKey, VarName> for LazyNumericSystem<VarKey, TermKey, VarName>
{
    fn get_term(&self, term_key: TermKey) -> NumericTerm<VarKey, TermKey> {
        self.inner.borrow().get_term(term_key)
    }

    fn evaluate_term(&self, term_key: TermKey, assignment: &HashMap<VarKey, Number>) -> Number {
        self.inner.borrow().evaluate_term(term_key, assignment)
    }
}

#[macro_export]
macro_rules! numeric_term {
    // Infinity
    (inf; $system:expr) => {
        $system.terms.get_or_insert_key($crate::systems::numeric::numeric_term::NumericTerm::Const($crate::systems::numeric::number::Number::Inf))
    };
    // const
    ($num:literal; $system:expr) => {
        $system.terms.get_or_insert_key($crate::systems::numeric::numeric_term::NumericTerm::Const($crate::systems::numeric::number::Number::Val($num)))
    };
    // var
    ($id:ident; $system:expr) => {{
        let var_key = $system.names.get_or_insert_key(stringify!($id));
        $system.terms.get_or_insert_key($crate::systems::numeric::numeric_term::NumericTerm::Var(var_key))
    }};
    // add
    (($lhs:tt + $rhs:tt); $system:expr) => {{
        let lhs = $crate::numeric_term!($lhs; $system);
        let rhs = $crate::numeric_term!($rhs; $system);
        $system.terms.get_or_insert_key($crate::systems::numeric::numeric_term::NumericTerm::Add(lhs, rhs))
    }};
    // mult
    (($lhs:tt * $rhs:tt); $system:expr) => {{
        let lhs = $crate::numeric_term!($lhs; $system);
        let rhs = $crate::numeric_term!($rhs; $system);
        $system.terms.get_or_insert_key($crate::systems::numeric::numeric_term::NumericTerm::Mult(lhs, rhs))
    }};
    // min
    ((min($($elem:tt),*)); $system:expr) => {{
        let mut terms = std::collections::BTreeSet::new();
        $(
            terms.insert($crate::numeric_term!($elem; $system));
        )*
        $system.terms.get_or_insert_key($crate::systems::numeric::numeric_term::NumericTerm::Min(terms))
    }};
    // max
    ((max($($elem:tt),*)); $system:expr) => {{
        let mut terms = std::collections::BTreeSet::new();
        $(
            terms.insert($crate::numeric_term!($elem; $system));
        )*
        $system.terms.get_or_insert_key($crate::systems::numeric::numeric_term::NumericTerm::Max(terms))
    }};
}

#[macro_export]
macro_rules! numeric_def {
    ($id:ident = $term:tt; $system:expr) => {{
        let term = $crate::numeric_term!($term; $system);
        let key = $system.names.get_or_insert_key(stringify!($id));
        $system.definitions.insert(key, term)
    }};
}

#[macro_export]
macro_rules! numeric_system {
    ($($id:ident = $term:tt;)*) => {
        {
            let mut system = $crate::systems::numeric::numeric_system::NumericSystemImpl::<usize, usize, &str>::default();
            $(
                $crate::numeric_def!($id = $term; system);
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
    fn numeric_system_infinity() {
        let sys = numeric_system! {
            x = inf;
        };
        for (key, term) in &sys.definitions {
            let var = *sys.names.get_value(key);
            match var {
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "inf"),
                &_ => panic!("{var} not found"),
            }
        }
    }

    #[test]
    fn numeric_system_literals() {
        let sys = numeric_system! {
            x = 3;
            y = 2;
            z = 5;
        };
        for (key, term) in &sys.definitions {
            let var = *sys.names.get_value(key);
            match var {
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "3"),
                "y" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "2"),
                "z" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "5"),
                &_ => panic!("{var} not found"),
            }
        }
    }

    #[test]
    fn numeric_system_variables() {
        let sys = numeric_system! {
            x = y;
            y = z;
            z = 5;
        };
        for (key, term) in &sys.definitions {
            let var = *sys.names.get_value(key);
            match var {
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "y"),
                "y" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "z"),
                "z" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "5"),
                &_ => panic!("{var} not found"),
            }
        }
    }

    #[test]
    fn numeric_system_add() {
        let sys = numeric_system! {
            x = (y + k);
            y = z;
            z = 5;
            k = t;
            t = (v + 3);
            v = (4 + 2);
        };
        for (key, term) in &sys.definitions {
            let var = *sys.names.get_value(key);
            match var {
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "(y + k)"),
                "y" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "z"),
                "z" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "5"),
                "k" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "t"),
                "t" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "(v + 3)"),
                "v" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "(4 + 2)"),
                &_ => panic!("{var} not found"),
            }
        }
    }

    #[test]
    fn numeric_system_mult() {
        let sys = numeric_system! {
            x = (y * k);
            y = z;
            z = 5;
            k = t;
            t = (v * 3);
            v = (4 * 2);
        };
        for (key, term) in &sys.definitions {
            let var = *sys.names.get_value(key);
            match var {
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "(y * k)"),
                "y" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "z"),
                "z" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "5"),
                "k" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "t"),
                "t" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "(v * 3)"),
                "v" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "(4 * 2)"),
                &_ => panic!("{var} not found"),
            }
        }
    }

    #[test]
    fn numeric_system_min() {
        let sys = numeric_system! {
            x = (min(y, k));
            y = z;
            z = 5;
            k = t;
            t = (min(v, 3));
            v = (min(4, 2));
        };
        for (key, term) in &sys.definitions {
            let var = *sys.names.get_value(key);
            match var {
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "min(y, k)"),
                "y" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "z"),
                "z" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "5"),
                "k" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "t"),
                "t" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "min(v, 3)"),
                "v" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "min(4, 2)"),
                &_ => panic!("{var} not found"),
            }
        }
    }

    #[test]
    fn numeric_system_max() {
        let sys = numeric_system! {
            x = (max(y, k));
            y = z;
            z = 5;
            k = t;
            t = (max(v, 3));
            v = (max(4, 2));
        };
        for (key, term) in &sys.definitions {
            let var = *sys.names.get_value(key);
            match var {
                "x" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "max(y, k)"),
                "y" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "z"),
                "z" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "5"),
                "k" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "t"),
                "t" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "max(v, 3)"),
                "v" => assert_eq!(sys.terms.get_value(*term).to_string(&sys), "max(4, 2)"),
                &_ => panic!("{var} not found"),
            }
        }
    }

    #[test]
    fn numeric_system_evaluate_const() {
        let mut sys = numeric_system! {
            x = 1;
            z = inf;
        };
        let x = sys.names.get_or_insert_key("x");
        let z = sys.names.get_or_insert_key("z");
        assert_eq!(
            sys.evaluate(x, &HashMap::new()),
            crate::systems::numeric::number::Number::Val(1)
        );
        assert_eq!(
            sys.evaluate(z, &HashMap::new()),
            crate::systems::numeric::number::Number::Inf
        );
    }

    #[test]
    fn numeric_system_evaluate_var() {
        let mut sys = numeric_system! {
            x = z;
            z = 1;
            y = k;
            k = inf;
        };
        let x = sys.names.get_or_insert_key("x");
        let z = sys.names.get_or_insert_key("z");
        let y = sys.names.get_or_insert_key("y");
        let k = sys.names.get_or_insert_key("k");
        let mut map = HashMap::new();
        map.insert(z, crate::systems::numeric::number::Number::Val(1));
        map.insert(k, crate::systems::numeric::number::Number::Inf);
        assert_eq!(
            sys.evaluate(x, &map),
            crate::systems::numeric::number::Number::Val(1)
        );
        assert_eq!(
            sys.evaluate(y, &map),
            crate::systems::numeric::number::Number::Inf
        );
    }

    #[test]
    fn numeric_system_evaluate_add() {
        let mut sys = numeric_system! {
            x = (1 + 2);
            y = (1 + inf);
            z = (inf + inf);
        };
        let x = sys.names.get_or_insert_key("x");
        let y = sys.names.get_or_insert_key("y");
        let z = sys.names.get_or_insert_key("z");
        assert_eq!(
            sys.evaluate(x, &HashMap::new()),
            crate::systems::numeric::number::Number::Val(3)
        );
        assert_eq!(
            sys.evaluate(y, &HashMap::new()),
            crate::systems::numeric::number::Number::Inf
        );
        assert_eq!(
            sys.evaluate(z, &HashMap::new()),
            crate::systems::numeric::number::Number::Inf
        );
    }

    #[test]
    fn numeric_system_evaluate_mult() {
        let mut sys = numeric_system! {
            x = (3 * 2);
            y = (1 * inf);
            z = (inf * inf);
        };
        let x = sys.names.get_or_insert_key("x");
        let y = sys.names.get_or_insert_key("y");
        let z = sys.names.get_or_insert_key("z");
        assert_eq!(
            sys.evaluate(x, &HashMap::new()),
            crate::systems::numeric::number::Number::Val(6)
        );
        assert_eq!(
            sys.evaluate(y, &HashMap::new()),
            crate::systems::numeric::number::Number::Inf
        );
        assert_eq!(
            sys.evaluate(z, &HashMap::new()),
            crate::systems::numeric::number::Number::Inf
        );
    }

    #[allow(clippy::many_single_char_names)]
    #[test]
    fn numeric_system_evaluate_min() {
        let mut sys = numeric_system! {
            x = (min(7, 3));
            y = (min(inf, 3));
            z = (min(7, inf));
            k = (min(inf, inf));
            t = (min(4, 0, 0));
            u = (min(4, 4, inf, 2, 3));
        };
        let x = sys.names.get_or_insert_key("x");
        let y = sys.names.get_or_insert_key("y");
        let z = sys.names.get_or_insert_key("z");
        let k = sys.names.get_or_insert_key("k");
        let t = sys.names.get_or_insert_key("t");
        let u = sys.names.get_or_insert_key("u");
        assert_eq!(
            sys.evaluate(x, &HashMap::new()),
            crate::systems::numeric::number::Number::Val(3)
        );
        assert_eq!(
            sys.evaluate(y, &HashMap::new()),
            crate::systems::numeric::number::Number::Val(3)
        );
        assert_eq!(
            sys.evaluate(z, &HashMap::new()),
            crate::systems::numeric::number::Number::Val(7)
        );
        assert_eq!(
            sys.evaluate(k, &HashMap::new()),
            crate::systems::numeric::number::Number::Inf
        );
        assert_eq!(
            sys.evaluate(t, &HashMap::new()),
            crate::systems::numeric::number::Number::Val(0)
        );
        assert_eq!(
            sys.evaluate(u, &HashMap::new()),
            crate::systems::numeric::number::Number::Val(2)
        );
    }

    #[allow(clippy::many_single_char_names)]
    #[test]
    fn numeric_system_evaluate_max() {
        let mut sys = numeric_system! {
            x = (max(7, 3));
            y = (max(inf, 3));
            z = (max(7, inf));
            k = (max(inf, inf));
            t = (max(1, 3, 2));
            u = (max(1, 3, inf, 10, 40));
        };
        let x = sys.names.get_or_insert_key("x");
        let y = sys.names.get_or_insert_key("y");
        let z = sys.names.get_or_insert_key("z");
        let k = sys.names.get_or_insert_key("k");
        let t = sys.names.get_or_insert_key("t");
        let u = sys.names.get_or_insert_key("u");
        assert_eq!(
            sys.evaluate(x, &HashMap::new()),
            crate::systems::numeric::number::Number::Val(7)
        );
        assert_eq!(
            sys.evaluate(y, &HashMap::new()),
            crate::systems::numeric::number::Number::Inf
        );
        assert_eq!(
            sys.evaluate(z, &HashMap::new()),
            crate::systems::numeric::number::Number::Inf
        );
        assert_eq!(
            sys.evaluate(k, &HashMap::new()),
            crate::systems::numeric::number::Number::Inf
        );
        assert_eq!(
            sys.evaluate(t, &HashMap::new()),
            crate::systems::numeric::number::Number::Val(3)
        );
        assert_eq!(
            sys.evaluate(u, &HashMap::new()),
            crate::systems::numeric::number::Number::Inf
        );
    }

    #[allow(clippy::many_single_char_names)]
    #[test]
    fn numeric_system_evaluate() {
        let mut sys = numeric_system! {
            x = (max(y, z));
            y = (k * t);
            z = inf;
            k = 10;
            t = 3;
        };
        let x = sys.names.get_or_insert_key("x");
        let y = sys.names.get_or_insert_key("y");
        let z = sys.names.get_or_insert_key("z");
        let k = sys.names.get_or_insert_key("k");
        let t = sys.names.get_or_insert_key("t");
        let mut map = HashMap::new();
        map.insert(y, crate::systems::numeric::number::Number::Inf);
        map.insert(z, crate::systems::numeric::number::Number::Inf);
        map.insert(k, crate::systems::numeric::number::Number::Val(10));
        map.insert(t, crate::systems::numeric::number::Number::Val(3));
        assert_eq!(
            sys.evaluate(x, &map),
            crate::systems::numeric::number::Number::Inf
        );
        assert_eq!(
            sys.evaluate(y, &map),
            crate::systems::numeric::number::Number::Val(30)
        );
        assert_eq!(
            sys.evaluate(z, &map),
            crate::systems::numeric::number::Number::Inf
        );
        assert_eq!(
            sys.evaluate(k, &map),
            crate::systems::numeric::number::Number::Val(10)
        );
        assert_eq!(
            sys.evaluate(t, &map),
            crate::systems::numeric::number::Number::Val(3)
        );
    }
}
