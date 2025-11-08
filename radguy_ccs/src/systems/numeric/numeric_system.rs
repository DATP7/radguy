use itertools::iproduct;
use radguy::extension::TermSystem;
use radguy::{Arguments, PairUniverse, System, Universe};
use radguy::{Assignment, Set, Union, bislotmap::BiSlotMap};
use slotmap::{Key, SecondaryMap};
use std::cmp::{max, min};
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use crate::systems::numeric::number::Number;
use crate::systems::numeric::numeric_term::NumericTerm;

#[derive(Default, Debug)]
pub struct NumericSystem<K: Key, T: Key, N: Hash + Eq + Clone> {
    pub names: BiSlotMap<K, N>,
    pub definitions: SecondaryMap<K, T>,
    pub terms: BiSlotMap<T, NumericTerm<K, T>>,
}

impl<K: Key, T: Key, N: Hash + Eq + Clone> NumericSystem<K, T, N> {
    pub fn evaluate_term(&self, term_key: T, assignment: &dyn Assignment<K, Number>) -> Number {
        match self.terms.get_value(term_key) {
            NumericTerm::Const(num) => num.clone(),
            NumericTerm::Var(k) => assignment.get(k),
            NumericTerm::Add(lhs, rhs) => {
                self.evaluate_term(*lhs, assignment) + self.evaluate_term(*rhs, assignment)
            }
            NumericTerm::Mult(lhs, rhs) => {
                self.evaluate_term(*lhs, assignment) * self.evaluate_term(*rhs, assignment)
            }
            NumericTerm::Sub(lhs, rhs) => {
                self.evaluate_term(*lhs, assignment) - self.evaluate_term(*rhs, assignment)
            }
            NumericTerm::Div(lhs, rhs) => {
                self.evaluate_term(*lhs, assignment) / self.evaluate_term(*rhs, assignment)
            }
            NumericTerm::Min(lhs, rhs) => min(
                self.evaluate_term(*lhs, assignment),
                self.evaluate_term(*rhs, assignment),
            ),
            NumericTerm::Max(lhs, rhs) => max(
                self.evaluate_term(*lhs, assignment),
                self.evaluate_term(*rhs, assignment),
            ),
        }
    }

    pub fn term_arguments<ArgSet: Set<K> + Union + Default>(&self, term_key: T) -> ArgSet {
        match self.terms.get_value(term_key) {
            NumericTerm::Const(_) => ArgSet::default(),
            NumericTerm::Var(k) => {
                let mut set = ArgSet::default();
                set.insert(*k);
                set
            }
            NumericTerm::Add(lhs, rhs)
            | NumericTerm::Mult(lhs, rhs)
            | NumericTerm::Sub(lhs, rhs)
            | NumericTerm::Div(lhs, rhs)
            | NumericTerm::Max(lhs, rhs)
            | NumericTerm::Min(lhs, rhs) => self
                .term_arguments::<ArgSet>(*lhs)
                .union(self.term_arguments(*rhs)),
        }
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone + Debug> NumericSystem<K, T, N> {
    pub fn print_assignment(&self, a: &dyn Assignment<K, Number>) {
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

impl<K: Key, T: Key, N: Hash + Eq + Clone> Universe<HashSet<K>> for NumericSystem<K, T, N> {
    fn universe(&self) -> HashSet<K> {
        self.definitions.keys().collect()
    }
}

impl<K: Key, T: Key, N: Hash + Eq + Clone> PairUniverse<HashSet<(K, K)>>
    for NumericSystem<K, T, N>
{
    fn pair_universe(&self) -> HashSet<(K, K)> {
        iproduct!(self.names.keys(), self.names.keys()).collect()
    }
}

impl<VarKey: Key, TermKey: Key, VarName: Hash + Eq + Clone> System<VarKey, Number>
    for NumericSystem<VarKey, TermKey, VarName>
{
    fn evaluate(&self, key: VarKey, assignment: &dyn Assignment<VarKey, Number>) -> Number {
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.evaluate_term(*term_key, assignment)
    }

    fn bottom_assignment(&self) -> impl Assignment<VarKey, Number> {
        HashMap::new()
    }
}

impl<VarKey: Key, TermKey: Key, VarName: Hash + Eq + Clone> Arguments<VarKey, HashSet<VarKey>>
    for NumericSystem<VarKey, TermKey, VarName>
{
    fn arguments(&self, key: VarKey) -> HashSet<VarKey> {
        let term_key = self.definitions.get(key).expect("variable must be defined");
        self.term_arguments(*term_key)
    }
}

impl<VarKey: Key + Hash, TermKey: Key + Hash, VarName: Hash + Eq + Clone>
    TermSystem<VarKey, Number, TermKey> for NumericSystem<VarKey, TermKey, VarName>
{
    fn definition(&self, variable: VarKey) -> TermKey {
        *self
            .definitions
            .get(variable)
            .expect("variable should have a definition")
    }
}
