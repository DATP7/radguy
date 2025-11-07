use lalrpop_util::lalrpop_mod;

lalrpop_mod!(
    #[allow(clippy::all, clippy::pedantic, clippy::nursery, clippy::unwrap_used)]
    #[rustfmt::skip]
    pub grammar,
    "/systems/wccs/grammar.rs"
);

pub mod ast;
pub mod wccs_system;
