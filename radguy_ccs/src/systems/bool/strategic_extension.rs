use std::{
    cmp::min,
    collections::{HashMap, HashSet},
    fmt::{Debug, Display},
    hash::Hash,
    marker::PhantomData,
    ops::Add,
};

use radguy::{
    Assignment, Bottom, CopiedIter,
    arena::Key,
    extension::TermSystem,
    ordered::{
        extension::{StrategicExtension, StrategicExtensionOracle},
        strategy::{Strategy, StrategyItem, StrategyWeight, UnionWithBy},
    },
    set::bitset::BitSet,
};

use crate::systems::bool::{BoolSystem, BoolTerm};

#[derive(Default)]
pub struct StrategicBoolExtension<VS>(PhantomData<VS>);

#[expect(
    clippy::implicit_hasher,
    reason = "we don't want to specify the hasher everytime we construct StrategicBoolExtension"
)]
impl<K> StrategicBoolExtension<HashSet<K>> {
    #[must_use]
    pub fn hashset() -> Self {
        Self::default()
    }
}

impl<K> StrategicBoolExtension<BitSet<K>> {
    #[must_use]
    pub fn bitset() -> Self {
        Self::default()
    }
}

impl<VS> StrategicBoolExtension<VS> {
    #[must_use]
    pub fn as_oracle<K, V, T, N, VarStrat, PairStrat, S>(
        self,
    ) -> StrategicExtensionOracle<K, V, T, N, VS, VarStrat, PairStrat, S>
    where
        StrategicExtensionOracle<K, V, T, N, VS, VarStrat, PairStrat, S>: From<Self>,
    {
        self.into()
    }
}

impl<
    VarKey: Hash + Copy + Key,
    VarValue: Bottom + Clone,
    TermKey: Hash + Copy + Key,
    VarName: Hash + Copy + Eq,
    VS: for<'a> CopiedIter<'a, VarKey> + Debug,
    VarStrat: Strategy<VarKey> + Default + UnionWithBy<VarKey> + Debug,
    PairStrat: Strategy<(VarKey, VarKey)>
        + IntoIterator<Item = StrategyItem<(VarKey, VarKey)>>
        + FromIterator<StrategyItem<(VarKey, VarKey)>>
        + radguy::ordered::strategy::SliceRight<VarKey, VarKey, VarStrat>
        + Default
        + Clone,
    S: BoolSystem<VarKey, TermKey, VarName> + TermSystem<VarKey, VarValue, TermKey>,
> StrategicExtension<VarKey, VarValue, TermKey, VarName, VS, VarStrat, PairStrat, S>
    for StrategicBoolExtension<VS>
where
    HashMap<VarKey, VarValue>: Assignment<VarKey, bool>,
{
    fn depends(
        &self,
        x: TermKey,
        assignment: &HashMap<VarKey, VarValue>,
        strategy: &PairStrat,
        system: &S,
    ) -> VarStrat {
        let term = system.get_term(x);
        match term {
            BoolTerm::Variable(y) if !assignment.get_assignment(&y) => strategy.slice_right(y),
            BoolTerm::Variable(_) | BoolTerm::True | BoolTerm::False => VarStrat::default(),
            BoolTerm::Or(term_keys) => {
                // All terms are false and there exist a false term that x can influence
                if term_keys
                    .iter()
                    .all(|&term_key| !system.evaluate_term(term_key, assignment))
                {
                    let mut ret = VarStrat::default();
                    for term in term_keys {
                        ret.union_with_by(self.depends(term, assignment, strategy, system), min);
                    }
                    ret
                } else {
                    VarStrat::default()
                }
            }
            BoolTerm::And(term_keys) => {
                // Filter out true terms
                let term_keys = term_keys
                    .iter()
                    .copied()
                    .filter(|&term_key| !system.evaluate_term(term_key, assignment));

                let mut ret = VarStrat::default();
                for term in term_keys {
                    ret.union_with_by(
                        self.depends(term, assignment, strategy, system),
                        StrategyWeight::add,
                    );
                }
                ret
            }
        }
    }
}

impl<VS> Clone for StrategicBoolExtension<VS> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<VarKey, S> Display
    for StrategicBoolExtension<HashSet<VarKey, S>>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "StrategicBool:hashset")
    }
}

impl<VarKey> Display 
    for StrategicBoolExtension<BitSet<VarKey>>{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "StrategicBool:bitset")
    }
}
