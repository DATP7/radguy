use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Display,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Process<'a> {
    Nil,
    Named(&'a str),
    ActionPrefix {
        action: Action<'a>,
        process: Box<Process<'a>>,
    },
    Restriction {
        process: Box<Process<'a>>,
        // We use `BTreeSet` because it implements `Hash`
        restriction: BTreeSet<&'a str>,
    },
    Relabelling {
        process: Box<Process<'a>>,
        // We use `BTreeMap` because it implements `Hash`
        labels: BTreeMap<&'a str, &'a str>,
    },
    Sum(Box<Process<'a>>, Box<Process<'a>>),
    Compose(Box<Process<'a>>, Box<Process<'a>>),
}

impl<'a> Process<'a> {
    /// Parse a CCS process
    ///
    /// # Panics
    /// Panics if the process cannot be parsed
    #[must_use]
    pub fn parse(ccs: &'a str) -> Self {
        let parser = super::grammar::StateParser::new();
        parser.parse(ccs).expect("process should parse")
    }
}

#[derive(Clone, Debug)]
pub struct Binding<'a> {
    pub name: &'a str,
    pub value: Process<'a>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Action<'a> {
    Tau,
    Label { name: &'a str, is_complement: bool },
}

impl<'a> Action<'a> {
    #[must_use]
    pub fn can_syncronize(&self, other: &Action) -> bool {
        match (self, other) {
            (Action::Tau, _) | (_, Action::Tau) => false,
            (
                Action::Label {
                    name,
                    is_complement,
                },
                Action::Label {
                    name: other_name,
                    is_complement: other_is_complement,
                },
            ) => *name == *other_name && *is_complement != *other_is_complement,
        }
    }

    /// Parse an action
    ///
    /// # Panics
    /// Panics if the action cannot be parsed
    #[must_use]
    pub fn parse(ccs: &'a str) -> Self {
        let parser = super::grammar::ActionParser::new();
        parser.parse(ccs).expect("action should parse")
    }
}

impl Display for Action<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Tau => write!(f, "tau"),
            Self::Label {
                name,
                is_complement,
            } if *is_complement => write!(f, "'{name}"),
            Self::Label { name, .. } => write!(f, "{name}"),
        }
    }
}
