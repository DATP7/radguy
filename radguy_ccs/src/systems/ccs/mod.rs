use lalrpop_util::lalrpop_mod;

lalrpop_mod!(
    #[allow(clippy::all, clippy::pedantic, clippy::nursery, clippy::unwrap_used)]
    #[rustfmt::skip]
    pub grammar,
    "/systems/ccs/grammar.rs"
);

pub mod ast;
pub mod bisimulation_system;
pub mod strong_transition_system;
pub mod transition_system;
pub mod weak_transition_system;
