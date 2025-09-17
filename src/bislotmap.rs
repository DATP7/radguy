use std::{collections::HashMap, hash::Hash};

use slotmap::{Key, SlotMap};

#[derive(Debug)]
pub struct BiSlotMap<K: Key, V: Hash + Eq + Clone> {
    vals: SlotMap<K, V>,
    keys: HashMap<V, K>,
}

impl<K: Key, V: Hash + Eq + Clone> BiSlotMap<K, V> {
    pub fn get_value(&self, key: K) -> Option<&'_ V> {
        self.vals.get(key)
    }
    pub fn get_or_insert_key(&mut self, val: V) -> K {
        if let Some(key) = self.keys.get(&val) {
            *key
        } else {
            // TODO: fix clone :(
            let key = self.vals.insert(val.clone());
            self.keys.insert(val, key);
            key
        }
    }
}

impl<K: Key, V: Hash + Eq + Clone> Default for BiSlotMap<K, V> {
    fn default() -> Self {
        Self {
            vals: SlotMap::default(),
            keys: HashMap::default(),
        }
    }
}
