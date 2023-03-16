use quickcheck::{Arbitrary, Gen};

/// An enum for the various kinds of "things" to do to
/// binary search trees in a quicktest.
#[derive(Copy, Clone, Debug)]
pub(crate) enum Op<K, V> {
    /// Insert the K, V into the data structure
    Insert(K, V),
    /// Remove the K from the data structure
    Remove(K),
    /// Compare iterators
    Iter,
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
            2 => Op::Iter,
            _ => unreachable!(),
        }
    }
}
