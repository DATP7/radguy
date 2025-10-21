use lalrpop_util::lalrpop_mod;

lalrpop_mod!(
    #[allow(clippy::all, clippy::pedantic, clippy::nursery, clippy::unwrap_used)]
    #[rustfmt::skip]
    pub grammar,
    "/systems/ccs/grammar.rs"
);

pub mod ast;
pub mod strong_bisimulation_system;
pub mod strong_transition_generator;
