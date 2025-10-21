use std::collections::{HashMap, HashSet};

use slotmap::Key;

use crate::systems::ccs::ast::{Action, Binding};

pub trait TransitionSystem<'a, ProcKey: Key> {
    fn get_transitions(&self, process_key: ProcKey) -> HashMap<Action<'a>, HashSet<ProcKey>>;
    fn load_ast(&mut self, ast: Vec<Binding<'a>>);
    fn lookup_process_key(&self, name: &str) -> Option<&ProcKey>;
}
