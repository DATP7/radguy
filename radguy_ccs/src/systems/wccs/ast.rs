use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Display;

use crate::systems::numeric::Number;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Process<'a> {
    Nil,
    Named(&'a str),
    ActionPrefix {
        action: WeightedAction<'a>,
        process: Box<Process<'a>>,
    },
    Restriction {
        process: Box<Process<'a>>,
        // We use `BTreeSet` because it implements `Hash`
        restriction: BTreeSet<&'a str>,
    },
    ActionRelabelling {
        process: Box<Process<'a>>,
        // We use `BTreeMap` because it implements `Hash`
        labels: BTreeMap<&'a str, &'a str>,
    },
    PropositionRelabelling {
        process: Box<Process<'a>>,
        // We use `BTreeMap` because it implements `Hash`
        labels: BTreeMap<&'a str, &'a str>,
    },
    Sum(Box<Process<'a>>, Box<Process<'a>>),
    Compose(Box<Process<'a>>, Box<Process<'a>>),
    AtomicPropositions {
        propositions: Vec<&'a str>,
        process: Box<Process<'a>>,
    },
}

impl<'a> Process<'a> {
    /// Parse a CCS process
    ///
    /// # Panics
    /// Panics if the process cannot be parsed
    #[must_use]
    pub fn parse(ccs: &'a str) -> Self {
        let parser = super::grammar::ProcessParser::new();
        parser
            .parse(ccs)
            .unwrap_or_else(|_| panic!("process: ({ccs}) could not be parsed"))
    }
}

pub(crate) enum Relabeling<'a> {
    Action(&'a str, &'a str),
    Proposition(&'a str, &'a str),
}

#[derive(Clone, Debug)]
pub struct Binding<'a> {
    pub name: &'a str,
    pub process: Process<'a>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Action<'a> {
    Tau,
    Label { name: &'a str, is_complement: bool },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, Copy)]
pub struct WeightedAction<'a> {
    pub weight: Number,
    pub action: Action<'a>,
}

impl<'a> WeightedAction<'a> {
    #[must_use]
    pub fn parse(ccs: &'a str) -> Self {
        let parser = super::grammar::ActionParser::new();
        parser.parse(ccs).expect("action should parse")
    }
}

impl Display for WeightedAction<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.action {
            Action::Tau => write!(f, "<tau, {}>", self.weight),
            Action::Label {
                name,
                is_complement,
            } => {
                if is_complement {
                    write!(f, "<{name}!, {}>", self.weight)
                } else {
                    write!(f, "<{name}, {}>", self.weight)
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, path::Path};

    use super::*;
    use crate::systems::wccs::grammar::{ActionParser, ProcessParser, ProgramParser};
    use crate::{assert_bad, assert_good};

    #[test]
    fn test_parse_func() {
        let parser = ProgramParser::new();

        let good = [
            "S := mow:<a>.S;",
            "S := mow:<a>.S \\ {a, b};",
            "S := mow:<a>.S [a -> b, b->c];",
            "S := mow:<a!>.S;",
            "S := mow:<a,3>.S;",
            "S := mow:<a!, 3>.S;",
            "S := mow:<a, 3>.S;",
            "S := mow:dump:<a>.S;",
            "S := mow:dump:<a>.<b>.S;",
            "S := mow:dump:<a>.(mow:S);",
            "S := S1 | S2;",
            "S := S1 + S2;",
            "S := mow:S1 + <a>.S2;",
            r"
            S := mow:<a, 1>.T;
            T := dump:S;
            ",
            "S := mow:dump:<a>.mow:S;",
            "T := <a,0>.dump:S;",
            "T := mow:S [mow => dump];",
            "T := mow:S [mow => dump, dud => bib];",
            "T := mow:S [mow -> dump];",
            "T := mow:S [mow -> dump, dud -> bib];",
            "T := mow:S [mow -> dump] [dud => bib];",
            "T := mow:S [mow => dump] [dud => bib];",
            "T := mow:S [mow => dump] [dud -> bib];",
            "T := mow:S [mow -> dump] [dud -> bib];",
        ];

        let bad = [
            "S := <tau!>.S;",                        // No co tau
            "S = mow:<a>.S;",                        // wrong =
            "S := mow.<a>.S;",                       // . instead of :
            "S := mow.<a, -2>.S;",                   // negative num
            "S := mow.<a, 0.1>.S;",                  // decimal
            "S := mow.<a, a>.S;",                    // id instead of num
            "T := mow:S [mow -> dump, dud => bib];", // combining action and proposition relabeling
            "T := mow:S [mow => dump, dud -> bib];", // combining action and proposition relabeling
        ];

        assert_good!(good, parser);
        assert_bad!(bad, parser);
    }

    #[test]
    fn large_examples() {
        let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("systems/wccs");
        let entries = fs::read_dir(dir).expect("failed to read dir");
        let parser = ProgramParser::new();

        for entry in entries {
            let path = entry.expect("invalid dir entry").path();
            let wccs = fs::read_to_string(&path).expect("file should be readable as string");

            parser.parse(&wccs).unwrap_or_else(|_| {
                panic!(
                    "file: \"{}\" should parse",
                    path.to_str().expect("to_str should work")
                )
            });
        }
    }

    #[test]
    fn parse_action() {
        let parser = ActionParser::new();
        let action_str = "<dud!, 8>";

        let parsed_action = parser.parse(action_str).expect("Action should parse");

        let actual_action = WeightedAction {
            weight: Number::Val(8),
            action: Action::Label {
                name: "dud",
                is_complement: true,
            },
        };

        assert_eq!(
            parsed_action, actual_action,
            "Action: \"{action_str}\" not parsed correctly"
        );
    }

    #[test]
    fn parse_process() {
        let parser = ProcessParser::new();
        let action_str = "mow:S";

        let parsed_process = parser.parse(action_str).expect("Process should parse");

        let actual_process = Process::AtomicPropositions {
            propositions: Vec::from(["mow"]),
            process: Box::new(Process::Named("S")),
        };

        assert_eq!(
            parsed_process, actual_process,
            "Process: \"{action_str}\" not parsed correctly",
        );
    }
}
