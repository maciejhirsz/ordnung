//! # Ordnung
//!
//! Fast, vector-based map implementation that preserves insertion order.
//!
//! + Map is implemented as a binary tree over a `Vec` for storage, with only
//!   two extra words per entry for book-keeping on 64-bit architectures.
//! + A fast hash function with good random distribution is used to balance the
//!   tree. Ordnung makes no guarantees that the tree will be perfectly
//!   balanced, but key lookup should be approaching `O(log n)` in most cases.
//! + Tree traversal is always breadth-first and happens over a single
//!   continuous block of memory, which makes it cache friendly.
//! + Iterating over all entries is always `O(n)`, same as `Vec<(K, V)>`.
//! + Removing a value uses a sentinel and is `~O(log n)`.
//! + There are no buckets, so there is no need to re-bucket things when growing
//!   the map.
//!
//! ## When should you use this?
//!
//! + You need to preserve insertion order of the map.
//! + Iterating over the map is very performance sensitive.
//! + Your average map has fewer than 100 entries.
//! + You have no a priori knowledge about the final size of the map when you
//!   start creating it.
#![warn(missing_docs)]
#![cfg_attr(not(test), no_std)]
extern crate alloc;

use core::{
    borrow::Borrow,
    cell::Cell,
    cmp::Ordering,
    hash::{Hash, Hasher},
    iter::FromIterator,
    marker::PhantomData,
    num::NonZeroU32,
    ops::Index,
    {fmt, slice},
};

pub mod compact;
mod entry;
mod raw_entry;

use ahash::AHasher;

pub use compact::Vec;
pub use entry::*;
pub use raw_entry::*;
// use alloc::vec::Vec;

/// Iterator over the keys
pub struct Keys<'a, K, V> {
    inner: Iter<'a, K, V>,
}
impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline]
    fn next(&mut self) -> Option<&'a K> {
        self.inner.next().map(|(k, _)| k)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

//#[derive(Clone)]
/// Iterator over the values
pub struct Values<'a, K, V> {
    inner: Iter<'a, K, V>,
}
impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline]
    fn next(&mut self) -> Option<&'a V> {
        self.inner.next().map(|(_, v)| v)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

#[derive(Clone)]
struct Node<K, V> {
    // Key
    pub key: K,

    // Hash of the key
    pub hash: u64,

    // Value stored. We'll use `None` as a sentinel value for removed
    // entries.
    pub value: Option<V>,

    // Store vector index pointing to the `Node` for which `hash` is smaller
    // than that of this `Node`.
    pub left: Cell<Option<NonZeroU32>>,

    // Same as above but for `Node`s with hash larger than this one. If the
    // hash is the same, but keys are different, the lookup will default
    // to the right branch as well.
    pub right: Cell<Option<NonZeroU32>>,
}

impl<K, V> fmt::Debug for Node<K, V>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(
            &(&self.key, &self.value, self.left.get(), self.right.get()),
            f,
        )
    }
}

impl<K, V> PartialEq for Node<K, V>
where
    K: PartialEq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.hash == other.hash && self.key == other.key && self.value == other.value
    }
}

impl<K, V> Node<K, V> {
    #[inline]
    const fn new(key: K, value: V, hash: u64) -> Self {
        Node {
            key,
            hash,
            value: Some(value),
            left: Cell::new(None),
            right: Cell::new(None),
        }
    }
}

// `Cell` isn't `Sync`, but all of our writes are contained and require
// `&mut` access, ergo this is safe.
unsafe impl<K: Sync, V: Sync> Sync for Node<K, V> {}

/// A `HashSet`-like type that preserves insertion order - this means O(n) iteration
/// by insertion order and O(log(n)) lookup by key.
#[derive(Debug, Clone)]
pub struct Set<T, H = AHasher> {
    map: Map<T, (), H>,
}

impl<T> Set<T> {
    /// Create a new `Set`
    #[inline]
    pub fn new() -> Self {
        Self { map: Map::new() }
    }

    /// Create a new `Set` with a given capacity
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            map: Map::with_capacity(capacity),
        }
    }
}

impl<T, H> Set<T, H> {
    /// Returns the number of elements in the set.
    #[inline]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the map contains no elements.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// An iterator visiting all elements in insertion order.
    /// The iterator element type is `&T`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ordnung::Set;
    ///
    /// let mut map = Set::new();
    /// map.insert("a");
    /// map.insert("b");
    /// map.insert("c");
    ///
    /// let entries: Vec<_> = map.iter().collect();
    ///
    /// assert_eq!(
    ///     entries,
    ///     &[
    ///         &"a",
    ///         &"b",
    ///         &"c",
    ///     ],
    /// );
    /// ```
    pub fn iter(&self) -> SetIter<'_, T> {
        SetIter {
            inner: self.map.iter(),
        }
    }
}

impl<T, H> Set<T, H>
where
    T: Hash + Eq,
    H: Hasher + Default,
{
    /// Add a value to the set.
    ///
    /// If the set did not have this value present, `true` is returned.
    /// If the set did have this value present, `false` is returned.
    #[inline]
    pub fn insert(&mut self, val: T) -> bool {
        self.map.insert(val, ()).is_some()
    }

    /// Returns a reference to the value in the set, if any.
    #[inline]
    pub fn get<Q: ?Sized>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map.get_key_value(value).map(|(k, _)| k)
    }

    /// Returns `true` if the set contains this value
    #[inline]
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.map.contains_key(value)
    }
}

// Because keys can inserted in different order, the safe way to
// compare `Map`s is to iterate over one and check if the other
// has all the same keys.
impl<T> PartialEq for Set<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.map == other.map
    }
}

impl<T> Eq for Set<T> where T: Eq {}

// Because keys can inserted in different order, the safe way to
// compare `Map`s is to iterate over one and check if the other
// has all the same keys.
impl<T> PartialOrd for Set<T>
where
    T: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.map.partial_cmp(&other.map)
    }
}

impl<T> Ord for Set<T>
where
    T: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        self.map.cmp(&other.map)
    }
}

impl<T> IntoIterator for Set<T> {
    type Item = T;
    type IntoIter = SetIntoIter<T>;

    #[inline]
    fn into_iter(self) -> SetIntoIter<T> {
        SetIntoIter(self.map.into_iter())
    }
}

impl<'a, T> IntoIterator for &'a Set<T> {
    type Item = &'a T;
    type IntoIter = SetIter<'a, T>;

    #[inline]
    fn into_iter(self) -> SetIter<'a, T> {
        self.iter()
    }
}

/// Consuming iterator
pub struct SetIntoIter<T>(IntoIter<T, ()>);
impl<T> ExactSizeIterator for SetIntoIter<T> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<T> DoubleEndedIterator for SetIntoIter<T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, ())| k)
    }
}

impl<T> Iterator for SetIntoIter<T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k, ())| k)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

/// An iterator over the entries of a `Set`.
///
/// This struct is created by the [`iter`](./struct.Set.html#method.iter)
/// method on [`Set`](./struct.Set.html). See its documentation for more.
pub struct SetIter<'a, T> {
    inner: Iter<'a, T, ()>,
}

impl<'i, T> Iterator for SetIter<'i, T> {
    type Item = &'i T;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, ())| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<T> DoubleEndedIterator for SetIter<'_, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|(k, ())| k)
    }
}

impl<T> ExactSizeIterator for SetIter<'_, T> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

/// A `HashMap`-like type that preserves insertion order, implemented as a binary tree.
#[derive(Debug, Clone)]
pub struct Map<K, V, H = AHasher> {
    store: Vec<Node<K, V>>,
    hasher: PhantomData<H>,
}

enum FindResult<'find> {
    Hit(usize),
    Miss(Option<&'find Cell<Option<NonZeroU32>>>),
}

use FindResult::*;

impl<K, V> Map<K, V> {
    /// Create a new `Map`.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a `Map` with a given capacity
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Map {
            store: Vec::with_capacity(capacity),
            hasher: PhantomData,
        }
    }
}

impl<K, V, H> Map<K, V, H> {
    /// Returns the number of elements in the map.
    #[inline]
    pub fn len(&self) -> usize {
        self.store.len()
    }

    /// Returns `true` if the map contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.store.is_empty()
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory for reuse.
    #[inline]
    pub fn clear(&mut self) {
        self.store.clear();
    }

    /// An iterator visiting all key-value pairs in insertion order.
    /// The iterator element type is `(&K, &V)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ordnung::Map;
    ///
    /// let mut map = Map::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// let entries: Vec<_> = map.iter().collect();
    ///
    /// assert_eq!(
    ///     entries,
    ///     &[
    ///         (&"a", &1),
    ///         (&"b", &2),
    ///         (&"c", &3),
    ///     ],
    /// );
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            inner: self.store.iter(),
        }
    }

    /// An iterator visiting all key-value pairs in insertion order, with
    /// mutable references to the values. The iterator element type is
    /// (&K, &mut V).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ordnung::Map;
    ///
    /// let mut map = Map::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// // Update all values
    /// for (_, val) in map.iter_mut() {
    ///     *val *= 2;
    /// }
    ///
    /// // Check if values are doubled
    /// let entries: Vec<_> = map.iter().collect();
    ///
    /// assert_eq!(
    ///     entries,
    ///     &[
    ///         (&"a", &2),
    ///         (&"b", &4),
    ///         (&"c", &6),
    ///     ],
    /// );
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            inner: self.store.iter_mut(),
        }
    }
}

impl<K, V, H> Default for Map<K, V, H> {
    /// Create a new `Map` with a custom hasher.
    #[inline]
    fn default() -> Self {
        Map {
            store: Vec::new(),
            hasher: PhantomData,
        }
    }
}

impl<K, V, H> Map<K, V, H>
where
    K: Hash + Eq,
    H: Hasher + Default,
{
    /// An iterator visiting all keys in arbitrary order.
    /// The iterator element type is `&'a K`.
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { inner: self.iter() }
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`.
    pub fn values(&self) -> Values<'_, K, V> {
        Values { inner: self.iter() }
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ordnung::Map;
    ///
    /// let mut map = Map::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let hash = Self::hash_key(&key);

        match self.find(hash) {
            Hit(idx) => unsafe { self.store.get_unchecked_mut(idx).value.replace(value) },
            Miss(parent) => {
                if let Some(parent) = parent {
                    parent.set(NonZeroU32::new(self.store.len() as u32));
                }

                self.store.push(Node::new(key, value, hash));

                None
            }
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and
    /// `Eq` on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ordnung::Map;
    ///
    /// let mut map = Map::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        self.get_key_value(key).map(|(_, v)| v)
    }

    /// Returns a reference to the value corresponding to the key, along with the original key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and
    /// `Eq` on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ordnung::Map;
    ///
    /// let mut map = Map::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get_key_value<Q>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let hash = Self::hash_key(key);

        match self.find(hash) {
            Hit(idx) => {
                let node = unsafe { self.store.get_unchecked(idx) };

                node.value.as_ref().map(|v| (&node.key, v))
            }
            Miss(_) => None,
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but Hash and Eq
    /// on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ordnung::Map;
    ///
    /// let mut map = Map::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let hash = Self::hash_key(key);

        match self.find(hash) {
            Hit(idx) => unsafe { self.store.get_unchecked_mut(idx).value.as_mut() },
            Miss(_) => None,
        }
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and
    /// `Eq` on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ordnung::Map;
    ///
    /// let mut map = Map::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let hash = Self::hash_key(key);

        match self.find(hash) {
            Hit(idx) => unsafe { self.store.get_unchecked(idx).value.is_some() },
            Miss(_) => false,
        }
    }

    /// Get a mutable reference to entry at key. Inserts a new entry by
    /// calling `F` if absent.
    // TODO: Replace with entry API
    pub fn get_or_insert<F>(&mut self, key: K, fill: F) -> &mut V
    where
        F: FnOnce() -> V,
    {
        let hash = Self::hash_key(&key);

        match self.find(hash) {
            Hit(idx) => {
                let node = unsafe { self.store.get_unchecked_mut(idx) };

                if node.value.is_none() {
                    node.value = Some(fill());
                }

                node.value.as_mut().unwrap()
            }
            Miss(parent) => {
                let idx = self.store.len();

                if let Some(parent) = parent {
                    parent.set(NonZeroU32::new(self.store.len() as u32));
                }

                self.store.push(Node::new(key, fill(), hash));

                self.store[idx].value.as_mut().unwrap()
            }
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but `Hash` and
    /// `Eq` on the borrowed form must match those for the key type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ordnung::Map;
    ///
    /// let mut map = Map::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let hash = Self::hash_key(key);

        match self.find(hash) {
            Hit(idx) => unsafe { self.store.get_unchecked_mut(idx).value.take() },
            Miss(_) => return None,
        }
    }

    #[inline]
    fn find(&self, hash: u64) -> FindResult {
        if self.len() == 0 {
            return Miss(None);
        }

        let mut idx = 0;

        loop {
            let node = unsafe { self.store.get_unchecked(idx) };

            if hash < node.hash {
                match node.left.get() {
                    Some(i) => idx = i.get() as usize,
                    None => return Miss(Some(&node.left)),
                }
            } else if hash > node.hash {
                match node.right.get() {
                    Some(i) => idx = i.get() as usize,
                    None => return Miss(Some(&node.right)),
                }
            } else {
                return Hit(idx);
            }
        }
    }

    #[inline]
    fn hash_key<Q: Hash>(key: Q) -> u64 {
        // let mut hasher = fnv::FnvHasher::default();
        // let mut hasher = rustc_hash::FxHasher::default();
        let mut hasher = H::default();

        key.hash(&mut hasher);

        hasher.finish()
    }

    /// Creates a raw entry builder for the HashMap.
    ///
    /// Raw entries provide the lowest level of control for searching and
    /// manipulating a map. They must be manually initialized with a hash and
    /// then manually searched. After this, insertions into a vacant entry
    /// still require an owned key to be provided.
    ///
    /// Raw entries are useful for such exotic situations as:
    ///
    /// * Hash memoization
    /// * Deferring the creation of an owned key until it is known to be required
    /// * Using a search key that doesn't work with the Borrow trait
    /// * Using custom comparison logic without newtype wrappers
    ///
    /// Because raw entries provide much more low-level control, it's much easier
    /// to put the HashMap into an inconsistent state which, while memory-safe,
    /// will cause the map to produce seemingly random results. Higher-level and
    /// more foolproof APIs like `entry` should be preferred when possible.
    ///
    /// In particular, the hash used to initialized the raw entry must still be
    /// consistent with the hash of the key that is ultimately stored in the entry.
    /// This is because implementations of HashMap may need to recompute hashes
    /// when resizing, at which point only the keys are available.
    ///
    /// Raw entries give mutable access to the keys. This must not be used
    /// to modify how the key would compare or hash, as the map will not re-evaluate
    /// where the key should go, meaning the keys may become "lost" if their
    /// location does not reflect their state. For instance, if you change a key
    /// so that the map now contains keys which compare equal, search may start
    /// acting erratically, with two keys randomly masking each other. Implementations
    /// are free to assume this doesn't happen (within the limits of memory-safety).
    #[inline]
    pub fn raw_entry_mut(&mut self) -> RawEntryBuilderMut<'_, K, V, H> {
        RawEntryBuilderMut { map: self }
    }

    /// Creates a raw immutable entry builder for the HashMap.
    ///
    /// Raw entries provide the lowest level of control for searching and
    /// manipulating a map. They must be manually initialized with a hash and
    /// then manually searched.
    ///
    /// This is useful for
    /// * Hash memoization
    /// * Using a search key that doesn't work with the Borrow trait
    /// * Using custom comparison logic without newtype wrappers
    ///
    /// Unless you are in such a situation, higher-level and more foolproof APIs like
    /// `get` should be preferred.
    ///
    /// Immutable raw entries have very limited use; you might instead want `raw_entry_mut`.
    #[inline]
    pub fn raw_entry(&self) -> RawEntryBuilder<'_, K, V, H> {
        RawEntryBuilder { map: self }
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// use ordnung::Map;
    ///
    /// let mut letters = Map::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     let counter = letters.entry(ch).or_insert(0);
    ///     *counter += 1;
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<K, V, H>
    where
        K: Eq + Clone,
    {
        for (idx, n) in self.store.iter().enumerate() {
            if &key == &n.key {
                return Entry::Occupied(OccupiedEntry::new(idx, key, self));
            }
        }
        Entry::Vacant(VacantEntry::new(key, self))
    }
}

impl<K, V> IntoIterator for Map<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    #[inline]
    fn into_iter(self) -> IntoIter<K, V> {
        IntoIter(self.store.into_iter())
    }
}

/// Consuming iterator
pub struct IntoIter<K, V>(<Vec<Node<K, V>> as IntoIterator>::IntoIter);

impl<K, V> ExactSizeIterator for IntoIter<K, V> {
    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<K, V> DoubleEndedIterator for IntoIter<K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(n) = self.0.next_back() {
                if let Some(v) = n.value {
                    return Some((n.key, v));
                }
            } else {
                return None;
            }
        }
    }
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(n) = self.0.next() {
                if let Some(v) = n.value {
                    return Some((n.key, v));
                }
            } else {
                return None;
            }
        }
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<K, Q: ?Sized, V> Index<&Q> for Map<K, V>
where
    K: Eq + Hash + Borrow<Q>,
    Q: Eq + Hash,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the HashMap.
    fn index(&self, key: &Q) -> &V {
        self.get(key).expect("Key not found in Map")
    }
}

impl<'json, IK, IV, K, V> FromIterator<(IK, IV)> for Map<K, V>
where
    IK: Into<K>,
    IV: Into<V>,
    K: Hash + Eq,
{
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = (IK, IV)>,
    {
        let iter = iter.into_iter();
        let mut map = Map::with_capacity(iter.size_hint().0);

        for (key, value) in iter {
            map.insert(key.into(), value.into());
        }

        map
    }
}

// Because keys can inserted in different order, the safe way to
// compare `Map`s is to iterate over one and check if the other
// has all the same keys.
impl<K, V> PartialEq for Map<K, V>
where
    K: PartialEq,
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        for (a, b) in self.iter().zip(other.iter()) {
            if a != b {
                return false;
            }
        }

        return true;
    }
}

impl<K, V> Eq for Map<K, V>
where
    K: Eq,
    V: Eq,
{
}

// Because keys can inserted in different order, the safe way to
// compare `Map`s is to iterate over one and check if the other
// has all the same keys.
impl<K, V> PartialOrd for Map<K, V>
where
    K: PartialOrd,
    V: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        for (a, b) in self.iter().zip(other.iter()) {
            match a.partial_cmp(&b) {
                Some(Ordering::Equal) => {}
                other => return other,
            }
        }

        return self.len().partial_cmp(&other.len());
    }
}

impl<K, V> Ord for Map<K, V>
where
    K: Ord,
    V: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        for (a, b) in self.iter().zip(other.iter()) {
            match a.cmp(&b) {
                Ordering::Equal => {}
                other => return other,
            }
        }

        return self.len().cmp(&other.len());
    }
}

/// An iterator over the entries of a `Map`.
///
/// This struct is created by the [`iter`](./struct.Map.html#method.iter)
/// method on [`Map`](./struct.Map.html). See its documentation for more.
pub struct Iter<'a, K, V> {
    inner: slice::Iter<'a, Node<K, V>>,
}

/// A mutable iterator over the entries of a `Map`.
///
/// This struct is created by the [`iter_mut`](./struct.Map.html#method.iter_mut)
/// method on [`Map`](./struct.Map.html). See its documentation for more.
pub struct IterMut<'a, K, V> {
    inner: slice::IterMut<'a, Node<K, V>>,
}

impl<K, V> Iter<'_, K, V> {
    /// Create an empty iterator that always returns `None`
    pub fn empty() -> Self {
        Iter { inner: [].iter() }
    }
}

impl<'i, K, V> Iterator for Iter<'i, K, V> {
    type Item = (&'i K, &'i V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.inner.next() {
            let value = match node.value {
                Some(ref value) => value,
                None => continue,
            };

            return Some((&node.key, value));
        }

        None
    }
}

impl<K, V> DoubleEndedIterator for Iter<'_, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.inner.next_back() {
            let value = match node.value {
                Some(ref value) => value,
                None => continue,
            };

            return Some((&node.key, value));
        }

        None
    }
}

impl<K, V> ExactSizeIterator for Iter<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<K, V> IterMut<'_, K, V> {
    /// Create an empty iterator that always returns `None`
    pub fn empty() -> Self {
        IterMut {
            inner: [].iter_mut(),
        }
    }
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.inner.next() {
            let value = match node.value {
                Some(ref mut value) => value,
                None => continue,
            };

            return Some((&node.key, value));
        }

        None
    }
}

impl<K, V> DoubleEndedIterator for IterMut<'_, K, V> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.inner.next_back() {
            let value = match node.value {
                Some(ref mut value) => value,
                None => continue,
            };

            return Some((&node.key, value));
        }

        None
    }
}

impl<K, V> ExactSizeIterator for IterMut<'_, K, V> {
    fn len(&self) -> usize {
        self.inner.len()
    }
}

#[cfg(test)]
mod tests {
    mod map {
        use crate::Map;

        #[test]
        fn empty() {
            let map: Map<&str, u64> = Map::new();

            assert_eq!(map.get("foo"), None);
            assert_eq!(map.len(), 0);
            assert_eq!(map.is_empty(), true);
        }

        #[test]
        fn simple() {
            let mut map: Map<&str, u64> = Map::new();

            map.insert("foo", 42);

            assert_eq!(map.get("foo"), Some(&42));
            assert_eq!(map.len(), 1);
            assert_eq!(map.is_empty(), false);
        }

        #[test]
        fn iter() {
            let mut map: Map<&str, u64> = Map::new();

            let elements = [("foo", 0123), ("bar", 1234), ("baz", 2345), ("qux", 3456)];

            for &(k, v) in &elements {
                assert!(map.insert(k, v).is_none());
            }

            assert_eq!(map.iter().len(), elements.len());
            assert_eq!(map.clone().into_iter().len(), elements.len());

            assert_eq!(
                &map.iter().map(|(&k, &v)| (k, v)).collect::<Vec<_>>(),
                &elements
            );
            assert_eq!(&map.clone().into_iter().collect::<Vec<_>>(), &elements);

            let reversed_elements = elements.iter().cloned().rev().collect::<Vec<_>>();

            assert_eq!(
                &map.iter().rev().map(|(&k, &v)| (k, v)).collect::<Vec<_>>(),
                &reversed_elements
            );
            assert_eq!(
                &map.clone().into_iter().rev().collect::<Vec<_>>(),
                &reversed_elements
            );
        }
    }

    mod set {
        use crate::Set;

        #[test]
        fn empty() {
            let map: Set<&str> = Set::new();

            assert_eq!(map.get("foo"), None);
            assert_eq!(map.len(), 0);
            assert_eq!(map.is_empty(), true);
        }

        #[test]
        fn simple() {
            let mut map: Set<&str> = Set::new();

            map.insert("foo");

            assert_eq!(map.get("foo"), Some(&"foo"));
            assert_eq!(map.len(), 1);
            assert_eq!(map.is_empty(), false);
        }

        #[test]
        fn iter() {
            let mut map: Set<&str> = Set::new();

            let elements = ["foo", "bar", "baz", "qux"];

            for &v in &elements {
                assert!(!map.insert(v));
            }

            assert_eq!(map.iter().len(), elements.len());
            assert_eq!(map.clone().into_iter().len(), elements.len());

            assert_eq!(&map.iter().cloned().collect::<Vec<_>>(), &elements);
            assert_eq!(&map.clone().into_iter().collect::<Vec<_>>(), &elements);

            let reversed_elements = elements.iter().cloned().rev().collect::<Vec<_>>();

            assert_eq!(
                &map.iter().cloned().rev().collect::<Vec<_>>(),
                &reversed_elements
            );
            assert_eq!(
                &map.clone().into_iter().rev().collect::<Vec<_>>(),
                &reversed_elements
            );
        }
    }
}
