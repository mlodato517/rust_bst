#[cfg(test)]
extern crate quickcheck;

use quickcheck::{Arbitrary, Gen};
use std::ops::Deref;

/// An enum for the various kinds of "things" to do to
/// binary search trees in a quicktest.
#[derive(Copy, Clone, Debug)]
pub enum Op<K, V> {
    /// Insert the K, V into the data structure
    Insert(K, V),
    /// Remove the K from the data structure
    Remove(K),
    /// Check that the value for the key matches
    CheckGet(K),
}

impl<K, V> Arbitrary for Op<K, V>
where
    K: Arbitrary,
    V: Arbitrary,
{
    /// Tells quickcheck how to randomly choose an operation
    fn arbitrary(g: &mut Gen) -> Self {
        match g.choose(&[0, 1, 2]).unwrap() {
            0 => Op::Insert(K::arbitrary(g), V::arbitrary(g)),
            1 => Op::Remove(K::arbitrary(g)),
            _ => Op::CheckGet(K::arbitrary(g)),
        }
    }
}

/// Allows a quicktest to take 10x the input it would have normally
/// received.
#[derive(Clone, Debug)]
pub struct Large<T>(T);

impl<T> Deref for Large<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> Arbitrary for Large<Vec<T>>
where
    T: Arbitrary,
{
    /// Makes an entity that is 10x larger than `g.size()`
    fn arbitrary(g: &mut Gen) -> Self {
        let len = g.size() * 10;
        Large((0..len).map(|_| T::arbitrary(g)).collect())
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new((**self).shrink().map(Large))
    }
}
