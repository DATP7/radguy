use std::collections::{BTreeMap, BTreeSet};

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

pub struct Binding<'a> {
    pub name: &'a str,
    pub value: Process<'a>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Action<'a> {
    Tau,
    Label { name: &'a str, is_complement: bool },
}

impl Action<'_> {
    #[must_use]
    pub fn can_syncronize(&self, other: &Action) -> bool {
        match self {
            Action::Tau => false,
            Action::Label {
                name,
                is_complement,
            } => match other {
                Action::Tau => false,
                Action::Label {
                    name: other_name,
                    is_complement: other_is_complement,
                } => *name == *other_name && *is_complement != *other_is_complement,
            },
        }
    }
}
