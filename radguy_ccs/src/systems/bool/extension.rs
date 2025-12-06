use radguy::{
    Assignment, Set, SliceRight, Union, Universe,
    extension::{ExtensionOracle, LocalExtension},
    set::bitset::BitSet,
};

use std::{
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
};

use crate::systems::bool::{BoolSystem, BoolTerm, Key};

pub struct BoolExtension<TermKey, VarName, VarSet>(PhantomData<(TermKey, VarName, VarSet)>);

impl<TermKey, VarName, VarSet> BoolExtension<TermKey, VarName, VarSet> {
    #[must_use]
    pub fn as_oracle<VarKey, PairSet, System>(
        self,
    ) -> ExtensionOracle<VarKey, bool, TermKey, VarSet, PairSet, System, Self>
    where
        VarKey: Key + Hash,
        TermKey: Key + Hash,
        VarName: Hash + Eq + Clone,
        VarSet: Set<VarKey>
            + Union
            + Default
            + IntoIterator<Item = VarKey>
            + FromIterator<VarKey>
            + Debug,
        PairSet: SliceRight<VarKey, VarKey, VarSet> + Union + FromIterator<(VarKey, VarKey)>,
        System: BoolSystem<VarKey, TermKey, VarName> + Universe<VarSet>,
        Self: LocalExtension<VarKey, bool, TermKey, VarSet, PairSet, System>,
    {
        self.into()
    }
}

impl<TermKey, VarName, VarSet> Default for BoolExtension<TermKey, VarName, VarSet> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

#[expect(
    clippy::implicit_hasher,
    reason = "we don't want to specify the hasher everytime we construct BoolExtension"
)]
impl<K, T, N> BoolExtension<T, N, HashSet<K>> {
    #[must_use]
    pub fn hashset() -> Self {
        Self::default()
    }
}

impl<K, T, N> BoolExtension<T, N, BitSet<K>> {
    #[must_use]
    pub fn bitset() -> Self {
        Self::default()
    }
}

impl<TermKey, VarName, VarSet> Clone for BoolExtension<TermKey, VarName, VarSet> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<
    VarKey: Key + Hash,
    TermKey: Key + Hash,
    VarName: Hash + Eq + Clone,
    VarSet: Set<VarKey> + Union + Default + IntoIterator<Item = VarKey> + FromIterator<VarKey> + Debug,
    PairSet: SliceRight<VarKey, VarKey, VarSet>,
    System: BoolSystem<VarKey, TermKey, VarName> + Universe<VarSet>,
> LocalExtension<VarKey, bool, TermKey, VarSet, PairSet, System>
    for BoolExtension<TermKey, VarName, VarSet>
{
    fn depends(
        &self,
        term_key: TermKey,
        assignment: &HashMap<VarKey, bool>,
        possible: &PairSet,
        system: &System,
    ) -> VarSet {
        let term = system.get_term(term_key);
        match term {
            BoolTerm::Variable(y) if !assignment.get_assignment(&y) => possible.slice_right(y),
            BoolTerm::Variable(_) | BoolTerm::True | BoolTerm::False => VarSet::default(),
            BoolTerm::Or(term_keys) => {
                // All terms are false and there exist a false term that x can influence
                if term_keys
                    .iter()
                    .all(|&term_key| !system.evaluate_term(term_key, assignment))
                {
                    term_keys
                        .into_iter()
                        .flat_map(|t| self.depends(t, assignment, possible, system))
                        .collect()
                } else {
                    VarSet::default()
                }
            }
            BoolTerm::And(term_keys) => {
                // Filter out true terms
                let term_keys = term_keys
                    .iter()
                    .copied()
                    .filter(|&term_key| !system.evaluate_term(term_key, assignment));

                let mut ret = VarSet::default();

                // x can influence at least one false term and all false terms are dependent on some var (can change)
                for term in term_keys {
                    let term_deps = self.depends(term, assignment, possible, system);
                    if term_deps.is_empty() && !system.evaluate_term(term_key, assignment) {
                        return VarSet::default();
                    }
                    ret = ret.union(term_deps);
                }
                ret
            }
        }
    }
}

impl<VarKey, TermKey, VarName, S: ::std::hash::BuildHasher> Display
    for BoolExtension<TermKey, VarName, HashSet<VarKey, S>>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bool:hashset")
    }
}

impl<VarKey, TermKey, VarName> Display for BoolExtension<TermKey, VarName, BitSet<VarKey>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bool:bitset")
    }
}

