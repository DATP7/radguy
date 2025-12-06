use std::{
    cmp::min,
    ops::Add,
    fmt::Debug,
    collections::{HashMap, HashSet},
    hash::Hash,
    marker::PhantomData,
};

use radguy::{
    arena::Key,
    extension::TermSystem,
    strategic_extension::StrategicExtension,
    Assignment,
    ordered::strategy::{
        StrategyWeight,
        StrategyItem,
        UnionWithBy,
        Strategy
    },
    CopiedIter,
    strategic_extension::StrategicExtensionOracle,
    set::bitset::BitSet,
    Bottom,
};

use crate::systems::bool::{BoolSystem, BoolTerm};

#[derive(Default, Clone)]
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
    pub fn as_oracle<K, V, T, N, VarStrat, PairStrat, S>(self) -> StrategicExtensionOracle<K, V, T, N, VS, VarStrat, PairStrat, S> 
    where StrategicExtensionOracle<K, V, T, N, VS, VarStrat, PairStrat, S>: From<Self> {
        self.into()
    }
}

impl<
    VarKey: Hash + Copy + Key,
    VarValue: Bottom + Clone,
    TermKey: Hash + Copy + Key,
    VarName: Hash + Copy + Eq,
    VS: for<'a> CopiedIter<'a, VarKey> + Debug,
    VarStrat: Strategy<VarKey> + Default + UnionWithBy<VarKey>,
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
                        ret.union_with_by(
                            <Self as StrategicExtension<
                                VarKey,
                                VarValue,
                                TermKey,
                                VarName,
                                VS,
                                VarStrat,
                                PairStrat,
                                S,
                            >>::depends(
                                self, term, assignment, strategy, system
                            ),
                            min,
                        );
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
                        <Self as StrategicExtension<
                            VarKey,
                            VarValue,
                            TermKey,
                            VarName,
                            VS,
                            VarStrat,
                            PairStrat,
                            S,
                        >>::depends(
                            self, term, assignment, strategy, system
                        ),
                        StrategyWeight::add,
                    );
                }
                ret
            }
        }
    }
}

/*
fn oracle() -> radguy::extension::StrategicExtensionOracle<VarKey, VarValue, TermKey, PairStrat, S, Self>
where
    Self: Default,
{
    radguy::extension::StrategicExtensionOracle::from(Self::default())
}*/
//impl Display for StrategicBoolExtension {
//    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//        write!(f, "StratBool")
//    }
//}

//E: StrategicExtension<VarKey, VarValue, TermKey, VarName, PairStrat, S>,
//TermKey: Key + Hash + Copy,
//VarName: Hash + Eq + Copy,
//VarKey: Key + Eq + Hash + Copy,
//VarValue: Clone + Bottom + Not<Output = bool>,
//PairStrat: Strategy<(VarKey, VarKey)>
//    + FromIterator<StrategyItem<(VarKey, VarKey)>>
//    + IntoIterator<Item = StrategyItem<(VarKey, VarKey)>>
//    + GetWeight<(VarKey, VarKey)>
//    + Clone,
//S: BoolSystem<VarKey, TermKey, VarName>
//    + radguy::System<VarKey, VarValue>
//    + TermSystem<VarKey, VarValue, TermKey>,

/*impl StrategicBoolExtension {
    #[must_use]
    pub fn as_oracle<TermKey, VarName, VarKey, VarValue, PairStrat, S, E>(
        self,
    ) -> StrategicExtensionOracle<TermKey, VarName, VarKey, VarValue, PairStrat, S, Self>
    where
        TermKey: Hash + Copy,
        VarName: Hash + Eq + Clone,
        VarKey: Hash + Eq + Copy,
        VarValue: Bottom + Clone,
        PairStrat: Strategy<(VarKey, VarKey)>
            + FromIterator<StrategyItem<(VarKey, VarKey)>>
            + IntoIterator<Item = StrategyItem<(VarKey, VarKey)>>
            + GetWeight<(VarKey, VarKey)>
            + Clone,
        S: TermSystem<VarKey, VarValue, TermKey>,
        E: StrategicExtension<TermKey, VarName, VarKey, VarValue, PairStrat, S>,
        Self: StrategicExtension<TermKey, VarName, VarKey, VarValue, PairStrat, S>,
    {
        self.into()
    }
}

impl StrategicBoolExtension {
    #[must_use]
    pub const fn hashset() -> Self {
        Self
    }
}

impl StrategicBoolExtension {
    #[must_use]
    pub const fn bitset() -> Self {
        Self
    }
}*/
