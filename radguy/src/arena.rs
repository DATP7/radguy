use std::{collections::HashMap, fmt::Debug, hash::Hash, marker::PhantomData};

pub trait Key:
    Copy + Clone + Default + Eq + PartialEq + Ord + PartialOrd + Hash + Debug + From<usize> + 'static
{
    fn index(&self) -> usize;
}

impl Key for usize {
    fn index(&self) -> usize {
        *self
    }
}

#[derive(Clone, Debug)]
pub struct Arena<K, V> {
    items: Vec<V>,
    _phantom_data: PhantomData<K>,
}

impl<K, V> Default for Arena<K, V> {
    fn default() -> Self {
        Self {
            items: Vec::new(),
            _phantom_data: PhantomData,
        }
    }
}

impl<K, V> Arena<K, V> {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: Key, V> Arena<K, V> {
    #[must_use]
    #[track_caller]
    pub fn get(&self, key: K) -> &V {
        self.items
            .get(key.index())
            .expect("index should exist in arena")
    }

    #[must_use]
    #[track_caller]
    pub fn get_mut(&mut self, key: K) -> &mut V {
        self.items
            .get_mut(key.index())
            .expect("index should exist in arena")
    }

    pub fn insert(&mut self, value: V) -> K {
        self.items.push(value);
        (self.items.len() - 1).into()
    }

    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.items.iter().enumerate().map(|(k, v)| (k.into(), v))
    }

    pub fn keys(&self) -> impl Iterator<Item = K> + Clone {
        (0..(self.len())).map(K::from)
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.items.len()
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

impl<'a, K: Key, V> IntoIterator for &'a Arena<K, V> {
    type Item = (K, &'a V);

    type IntoIter = impl Iterator<Item = (K, &'a V)>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[derive(Clone, Debug)]
pub struct SecondaryArena<K, V> {
    values: Vec<Option<V>>,
    _phantom_data: PhantomData<K>,
}

impl<K, V> Default for SecondaryArena<K, V> {
    fn default() -> Self {
        Self {
            values: Vec::new(),
            _phantom_data: PhantomData,
        }
    }
}

impl<K, V> SecondaryArena<K, V> {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

impl<K: Key, V> SecondaryArena<K, V> {
    /// Insert a value with a given id into the arena, returning the previous value if there was
    /// any.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let idx = key.index();
        if self.values.len() <= idx {
            self.values.resize_with(idx + 1, || None);
        }
        self.values[idx].replace(value)
    }

    /// Get a value from a given id
    #[must_use]
    pub fn get(&self, key: K) -> Option<&V> {
        self.values.get(key.index()).and_then(Option::as_ref)
    }

    #[must_use]
    pub fn get_mut(&mut self, key: K) -> Option<&mut V> {
        self.values.get_mut(key.index()).and_then(Option::as_mut)
    }

    pub fn take(&mut self, key: K) -> Option<V> {
        self.values.get_mut(key.index()).and_then(Option::take)
    }

    pub fn replace_with<F: FnOnce(Option<V>) -> V>(&mut self, key: K, f: F) {
        let prev = self.take(key);
        self.insert(key, f(prev));
    }

    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.values
            .iter()
            .enumerate()
            .filter_map(|(k, v)| v.as_ref().map(|v| (k.into(), v)))
    }

    #[must_use]
    pub fn contains_key(&self, key: K) -> bool {
        self.values.get(key.index()).is_some_and(Option::is_some)
    }

    #[must_use]
    pub fn keys(&self) -> SecondaryArenaKeys<'_, K, V> {
        SecondaryArenaKeys {
            iter: self.values.iter().enumerate(),
            _phantom_data: self._phantom_data,
        }
    }

    #[must_use]
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        if self.values.len() <= key.index() {
            self.values.resize_with(key.index(), || None);
        }
        if self
            .values
            .get(key.index())
            .and_then(Option::as_ref)
            .is_some()
        {
            Entry::Occupied { arena: self, key }
        } else {
            Entry::Vacant { arena: self, key }
        }
    }
}

pub enum Entry<'a, K: Key, V> {
    Occupied {
        arena: &'a mut SecondaryArena<K, V>,
        key: K,
    },
    Vacant {
        arena: &'a mut SecondaryArena<K, V>,
        key: K,
    },
}

impl<'a, K: Key, V> Entry<'a, K, V> {
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied { arena, key } => arena
                .get_mut(key)
                .expect("value should exist for occupied entry"),
            Entry::Vacant { arena, key } => {
                arena.insert(key, default());
                arena
                    .get_mut(key)
                    .expect("arena should contain key after inserting")
            }
        }
    }

    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(V::default)
    }
}

impl<'a, K: Key, V> IntoIterator for &'a SecondaryArena<K, V> {
    type Item = (K, &'a V);

    type IntoIter = impl Iterator<Item = (K, &'a V)>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[derive(Clone, Debug)]
pub struct SecondaryArenaKeys<'a, K, V> {
    iter: std::iter::Enumerate<std::slice::Iter<'a, Option<V>>>,
    _phantom_data: PhantomData<K>,
}

impl<K: Key, V> Iterator for SecondaryArenaKeys<'_, K, V> {
    type Item = K;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .find_map(|(i, opt)| opt.as_ref().map(|_| i.into()))
    }
}

#[derive(Clone, Debug)]
pub struct BiArena<K, V> {
    vals: Arena<K, V>,
    keys: HashMap<V, K>,
}

impl<K, V> Default for BiArena<K, V> {
    fn default() -> Self {
        Self {
            vals: Arena::new(),
            keys: HashMap::new(),
        }
    }
}

impl<K: Key, V> BiArena<K, V> {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn iter(&self) -> impl Iterator<Item = (K, &V)> {
        self.vals.iter()
    }

    pub fn keys(&self) -> impl Iterator<Item = K> + Clone {
        self.vals.keys()
    }
}

impl<K: Key, V: Hash + Eq + Clone> BiArena<K, V> {
    #[must_use]
    #[track_caller]
    pub fn get_value(&self, key: K) -> &V {
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

    pub fn contains_value(&self, val: &V) -> bool {
        self.keys.contains_key(val)
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.vals.len()
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.vals.is_empty()
    }
}

impl<'a, K: Key, V: 'a> IntoIterator for &'a BiArena<K, V> {
    type Item = (K, &'a V);
    type IntoIter = impl Iterator<Item = (K, &'a V)>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
