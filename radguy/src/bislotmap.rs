use std::{collections::HashMap, hash::Hash};

use slotmap::{Key, SlotMap};

#[derive(Clone, Debug)]
pub struct BiSlotMap<K: Key, V: Hash + Eq + Clone> {
    vals: SlotMap<K, V>,
    keys: HashMap<V, K>,
}

impl<K: Key, V: Hash + Eq + Clone> BiSlotMap<K, V> {
    pub fn get_value(&self, key: K) -> &'_ V {
        self.vals.get(key).expect("key should exist in bislotmap")
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

    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.vals.iter()
    }

    #[must_use]
    pub fn keys(&self) -> slotmap::basic::Keys<'_, K, V> {
        self.vals.keys()
    }

    pub fn contains_value(&self, val: &V) -> bool {
        self.keys.contains_key(val)
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
