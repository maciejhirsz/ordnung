// based on / take from <https://github.com/rust-lang/hashbrown/blob/62a1ae24d4678fcbf777bef6b205fadeecb781d9/src/map.rs>

use super::*;
use core::mem;

/// A builder for computing where in a [`VecMap`] a key-value pair would be stored.
///
/// See the [`VecMap::raw_entry_mut`] docs for usage examples.
///
/// [`VecMap::raw_entry_mut`]: struct.VecMap.html#method.raw_entry_mut
pub struct RawEntryBuilderMut<'a, K, V, H> {
    pub(crate) map: &'a mut Map<K, V, H>,
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This is a lower-level version of [`Entry`].
///
/// This `enum` is constructed through the [`raw_entry_mut`] method on [`VecMap`],
/// then calling one of the methods of that [`RawEntryBuilderMut`].
///
/// [`VecMap`]: struct.VecMap.html
/// [`Entry`]: enum.Entry.html
/// [`raw_entry_mut`]: struct.VecMap.html#method.raw_entry_mut
/// [`RawEntryBuilderMut`]: struct.RawEntryBuilderMut.html
pub enum RawEntryMut<'a, K, V, H> {
    /// An occupied entry.
    Occupied(RawOccupiedEntryMut<'a, K, V, H>),
    /// A vacant entry.
    Vacant(RawVacantEntryMut<'a, K, V, H>),
}

/// A view into an occupied entry in a `VecMap`.
/// It is part of the [`RawEntryMut`] enum.
///
/// [`RawEntryMut`]: enum.RawEntryMut.html
pub struct RawOccupiedEntryMut<'a, K, V, H> {
    idx: usize,
    map: &'a mut Map<K, V, H>,
}

unsafe impl<K, V, H> Send for RawOccupiedEntryMut<'_, K, V, H>
where
    K: Send,
    V: Send,
{
}
unsafe impl<K, V, H> Sync for RawOccupiedEntryMut<'_, K, V, H>
where
    K: Sync,
    V: Sync,
{
}

/// A view into a vacant entry in a `VecMap`.
/// It is part of the [`RawEntryMut`] enum.
///
/// [`RawEntryMut`]: enum.RawEntryMut.html
pub struct RawVacantEntryMut<'a, K, V, H> {
    map: &'a mut Map<K, V, H>,
}

/// A builder for computing where in a [`VecMap`] a key-value pair would be stored.
///
/// See the [`VecMap::raw_entry`] docs for usage examples.
///
/// [`VecMap::raw_entry`]: struct.VecMap.html#method.raw_entry
pub struct RawEntryBuilder<'a, K, V, H> {
    pub(crate) map: &'a Map<K, V, H>,
}

impl<'a, K, V, H> RawEntryBuilderMut<'a, K, V, H> {
    /// Creates a `RawEntryMut` from the given key.
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_key<Q: ?Sized>(self, k: &Q) -> RawEntryMut<'a, K, V, H>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        self.from_key_hashed_nocheck(0, k)
    }

    /// Creates a `RawEntryMut` from the given key and its hash.
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_key_hashed_nocheck<Q: ?Sized>(self, hash: u64, k: &Q) -> RawEntryMut<'a, K, V, H>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        self.from_hash(hash, |q| q.borrow().eq(k))
    }
}

impl<'a, K, V, H> RawEntryBuilderMut<'a, K, V, H> {
    /// Creates a `RawEntryMut` from the given hash.
    /// Note for the vec mapo hash has no effect it is only
    /// provided for convinience reasons
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_hash<F>(self, _hash: u64, is_match: F) -> RawEntryMut<'a, K, V, H>
    where
        for<'b> F: FnMut(&'b K) -> bool,
    {
        self.search(is_match)
    }

    #[inline]
    fn search<F>(self, mut is_match: F) -> RawEntryMut<'a, K, V, H>
    where
        for<'b> F: FnMut(&'b K) -> bool,
    {
        for (idx, n) in self.map.store.iter().enumerate() {
            if n.value.is_some() && is_match(&n.key) {
                return RawEntryMut::Occupied(RawOccupiedEntryMut { idx, map: self.map });
            }
        }
        RawEntryMut::Vacant(RawVacantEntryMut { map: self.map })
    }
}

impl<'a, K, V, H> RawEntryBuilder<'a, K, V, H> {
    /// Access an entry by key.
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_key<Q: ?Sized>(self, k: &Q) -> Option<(&'a K, &'a V)>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        self.from_key_hashed_nocheck(0, k)
    }

    /// Access an entry by a key and its hash.
    /// Note hash has no effect for `VecMap`
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_key_hashed_nocheck<Q: ?Sized>(self, hash: u64, k: &Q) -> Option<(&'a K, &'a V)>
    where
        K: Borrow<Q>,
        Q: Eq,
    {
        self.from_hash(hash, |q| q.borrow().eq(k))
    }

    #[inline]
    fn search<F>(self, _hash: u64, mut is_match: F) -> Option<(&'a K, &'a V)>
    where
        F: FnMut(&K) -> bool,
    {
        for n in self.map.store.iter() {
            if let Some(v) = &n.value {
                if is_match(&n.key) {
                    return Some((&n.key, v));
                }
            }
        }
        None
    }

    /// Access an entry by hash.
    #[inline]
    #[allow(clippy::wrong_self_convention)]
    pub fn from_hash<F>(self, hash: u64, is_match: F) -> Option<(&'a K, &'a V)>
    where
        F: FnMut(&K) -> bool,
    {
        self.search(hash, is_match)
    }
}

impl<'a, K, V, H> RawEntryMut<'a, K, V, H>
where
    K: Eq + Hash + Clone,
    H: Hasher + Default,
{
    /// Sets the value of the entry, and returns a RawOccupiedEntryMut.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordnung::Map;
    ///
    /// let mut map: Map<&str, u32> = Map::new();
    /// let entry = map.raw_entry_mut().from_key("horseyland").insert("horseyland", 37);
    ///
    /// assert_eq!(entry.remove_entry(), ("horseyland", 37));
    /// ```
    #[inline]
    pub fn insert(self, key: K, value: V) -> RawOccupiedEntryMut<'a, K, V, H> {
        match self {
            RawEntryMut::Occupied(mut entry) => {
                entry.insert(value);
                entry
            }
            RawEntryMut::Vacant(entry) => entry.insert_entry(key, value),
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// mutable references to the key and value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordnung::Map;
    ///
    /// let mut map: Map<&str, u32> = Map::new();
    ///
    /// map.raw_entry_mut().from_key("poneyland").or_insert("poneyland", 3);
    /// assert_eq!(map["poneyland"], 3);
    ///
    /// *map.raw_entry_mut().from_key("poneyland").or_insert("poneyland", 10).1 *= 2;
    /// assert_eq!(map["poneyland"], 6);
    /// ```
    #[inline]
    pub fn or_insert(self, default_key: K, default_val: V) -> (&'a mut K, &'a mut V) {
        match self {
            RawEntryMut::Occupied(entry) => entry.into_key_value(),
            RawEntryMut::Vacant(entry) => entry.insert(default_key, default_val),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns mutable references to the key and value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordnung::Map;
    ///
    /// let mut map: Map<&str, String> = Map::new();
    ///
    /// map.raw_entry_mut().from_key("poneyland").or_insert_with(|| {
    ///     ("poneyland", "hoho".to_string())
    /// });
    ///
    /// assert_eq!(map["poneyland"], "hoho".to_string());
    /// ```
    #[inline]
    pub fn or_insert_with<F>(self, default: F) -> (&'a mut K, &'a mut V)
    where
        F: FnOnce() -> (K, V),
    {
        match self {
            RawEntryMut::Occupied(entry) => entry.into_key_value(),
            RawEntryMut::Vacant(entry) => {
                let (k, v) = default();
                entry.insert(k, v)
            }
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordnung::Map;
    ///
    /// let mut map: Map<&str, u32> = Map::new();
    ///
    /// map.raw_entry_mut()
    ///    .from_key("poneyland")
    ///    .and_modify(|_k, v| { *v += 1 })
    ///    .or_insert("poneyland", 42);
    /// assert_eq!(map["poneyland"], 42);
    ///
    /// map.raw_entry_mut()
    ///    .from_key("poneyland")
    ///    .and_modify(|_k, v| { *v += 1 })
    ///    .or_insert("poneyland", 0);
    /// assert_eq!(map["poneyland"], 43);
    /// ```
    #[inline]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut K, &mut V),
    {
        match self {
            RawEntryMut::Occupied(mut entry) => {
                {
                    let (k, v) = entry.get_key_value_mut();
                    f(k, v);
                }
                RawEntryMut::Occupied(entry)
            }
            RawEntryMut::Vacant(entry) => RawEntryMut::Vacant(entry),
        }
    }
}

impl<'a, K, V, H> RawOccupiedEntryMut<'a, K, V, H>
where
    K: Clone,
{
    /// Gets a reference to the key in the entry.
    #[inline]
    pub fn key(&self) -> &K {
        unsafe { &self.map.store.get_unchecked(self.idx).key }
    }

    /// Gets a mutable reference to the key in the entry.
    #[inline]
    pub fn key_mut(&mut self) -> &mut K {
        unsafe { &mut self.map.store.get_unchecked_mut(self.idx).key }
    }

    /// Converts the entry into a mutable reference to the key in the entry
    /// with a lifetime bound to the map itself.
    #[inline]
    pub fn into_key(self) -> &'a mut K {
        unsafe { &mut self.map.store.get_unchecked_mut(self.idx).key }
    }

    /// Gets a reference to the value in the entry.
    #[inline]
    pub fn get(&self) -> &V {
        if let Some(v) = unsafe { &self.map.store.get_unchecked(self.idx).value } {
            v
        } else {
            unreachable!()
        }
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        if let Some(v) = unsafe { &mut self.map.store.get_unchecked_mut(self.idx).value } {
            v
        } else {
            unreachable!()
        }
    }

    /// Gets a mutable reference to the value in the entry.
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        if let Some(v) = unsafe { &mut self.map.store.get_unchecked_mut(self.idx).value } {
            v
        } else {
            unreachable!()
        }
    }

    /// Gets a reference to the key and value in the entry.
    #[inline]
    pub fn get_key_value(&mut self) -> (&K, &V) {
        unsafe {
            let n = &self.map.store.get_unchecked(self.idx);
            if let Some(v) = &n.value {
                (&n.key, v)
            } else {
                unreachable!()
            }
        }
    }

    /// Gets a mutable reference to the key and value in the entry.
    #[inline]
    pub fn get_key_value_mut(&mut self) -> (&mut K, &mut V) {
        unsafe {
            if let Node {
                value: Some(v),
                key,
                ..
            } = self.map.store.get_unchecked_mut(self.idx)
            {
                (key, v)
            } else {
                unreachable!()
            }
        }
    }

    /// Converts the OccupiedEntry into a mutable reference to the key and value in the entry
    /// with a lifetime bound to the map itself.
    #[inline]
    pub fn into_key_value(self) -> (&'a mut K, &'a mut V) {
        unsafe {
            if let Node {
                value: Some(v),
                key,
                ..
            } = self.map.store.get_unchecked_mut(self.idx)
            {
                (key, v)
            } else {
                unreachable!()
            }
        }
    }

    /// Sets the value of the entry, and returns the entry's old value.
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        mem::replace(self.get_mut(), value)
    }

    /// Sets the value of the entry, and returns the entry's old value.
    #[inline]
    pub fn insert_key(&mut self, key: K) -> K {
        mem::replace(self.key_mut(), key)
    }

    /// Takes the value out of the entry, and returns it.
    #[inline]
    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    /// Take the ownership of the key and value from the map.
    #[inline]
    pub fn remove_entry(self) -> (K, V) {
        let n = unsafe { self.map.store.get_unchecked_mut(self.idx) };

        let v = n.value.take().unwrap();

        (n.key.clone(), v)
    }
}

impl<'a, K, V, H> RawVacantEntryMut<'a, K, V, H>
where
    K: Eq + Hash,
    H: Hasher + Default,
{
    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it.
    #[inline]
    pub fn insert(self, key: K, value: V) -> (&'a mut K, &'a mut V) {
        let idx = self.map.store.len();
        self.map.insert(key, value);

        unsafe {
            if let Node {
                value: Some(v),
                key,
                ..
            } = self.map.store.get_unchecked_mut(idx)
            {
                (key, v)
            } else {
                unreachable!()
            }
        }
    }

    /// Sets the value of the entry with the VacantEntry's key,
    /// and returns a mutable reference to it.
    #[inline]
    #[allow(clippy::shadow_unrelated)]
    pub fn insert_hashed_nocheck(self, _hash: u64, key: K, value: V) -> (&'a mut K, &'a mut V) {
        self.insert(key, value)
    }

    /// Set the value of an entry with a custom hasher function.
    #[inline]
    pub fn insert_with_hasher(
        self,
        _hash: u64,
        key: K,
        value: V,
        _hasher: H,
    ) -> (&'a mut K, &'a mut V)
    where
        H: Fn(&K) -> u64,
    {
        self.insert(key, value)
    }

    #[inline]
    fn insert_entry(self, key: K, value: V) -> RawOccupiedEntryMut<'a, K, V, H> {
        let idx = self.map.store.len();
        self.map.insert(key, value);
        RawOccupiedEntryMut { idx, map: self.map }
    }
}

/*
impl<K, V, S> Debug for RawEntryBuilderMut<'_, K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawEntryBuilder").finish()
    }
}

impl<K, V> Debug for RawEntryMut<'_, K, V>
where
    K: Debug,
    V: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            RawEntryMut::Vacant(ref v) => f.debug_tuple("RawEntry").field(v).finish(),
            RawEntryMut::Occupied(ref o) => f.debug_tuple("RawEntry").field(o).finish(),
        }
    }
}

impl<K: Debug, V: Debug, S> Debug for RawOccupiedEntryMut<'_, K, V, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawOccupiedEntryMut")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}

impl<K, V, S> Debug for RawVacantEntryMut<'_, K, V, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawVacantEntryMut").finish()
    }
}

impl<K, V, S> Debug for RawEntryBuilder<'_, K, V, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RawEntryBuilder").finish()
    }
}
*/
