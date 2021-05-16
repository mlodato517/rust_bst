//! A Functional BST. This is modeled after a BST one would see in
//! a functional language like Haskell. Any operations that one would
//! expect to modify the tree (e.g. `insert` or `delete`) instead return
//! a new tree that reference many of the nodes of the original tree.
//!
//! To avoid copious `Rc`ing, we do not implement a particularly efficient
//! persistent structure - we only allow one tree at a time. Still, most
//! of the algorithms are the same and there are useful lessons to learn!

use std::cmp;

/// A `Node` has a key that is used for searching/sorting and a value
/// that is associated with that key. Either of its children may be
/// present or absent.
#[derive(Clone)]
struct Node<K, V> {
    key: K,
    value: V,
    left: Option<Box<Node<K, V>>>,
    right: Option<Box<Node<K, V>>>,
}

impl<K, V> Node<K, V> {
    /// Creates a new `Node` with the given key and value
    /// and no children
    fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            left: None,
            right: None,
        }
    }

    /// Returns the largest node in this subtree and a new subtree
    /// without that largest node.
    fn delete_largest(self) -> (K, V, Option<Box<Self>>)
    where
        K: cmp::Ord,
    {
        match self.right {
            None => (self.key, self.value, self.left),
            Some(right) => {
                let (k, v, sub) = right.delete_largest();

                (k, v, Some(Box::new(Self { right: sub, ..self })))
            }
        }
    }

    /// Returns a new `Node` whose subtree contains a `Node`
    /// with the given key and value.
    fn insert(self, key: K, value: V) -> Self
    where
        K: cmp::Ord,
    {
        match key.cmp(&self.key) {
            cmp::Ordering::Less => Self {
                left: match self.left {
                    None => Some(Box::new(Self::new(key, value))),
                    Some(left) => Some(Box::new(left.insert(key, value))),
                },
                ..self
            },
            cmp::Ordering::Equal => Self { value, ..self },
            cmp::Ordering::Greater => Self {
                right: match self.right {
                    None => Some(Box::new(Self::new(key, value))),
                    Some(right) => Some(Box::new(right.insert(key, value))),
                },
                ..self
            },
        }
    }

    /// Potentially finds the value associated with the given key
    /// in this `Node`. If no node has the corresponding key, `None`
    /// is returned.
    fn find(&self, k: &K) -> Option<&V>
    where
        K: cmp::Ord,
    {
        match k.cmp(&self.key) {
            cmp::Ordering::Less => self.left.as_ref().and_then(|left| left.find(k)),
            cmp::Ordering::Equal => Some(&self.value),
            cmp::Ordering::Greater => self.right.as_ref().and_then(|right| right.find(k)),
        }
    }

    /// Returns a new `Node` without a node with the given key.
    /// If the subtree contained a node with the key, it is removed.
    /// If the subtree never contained a node with the key, a new
    /// subtree is constructed that is identical to the previous.
    fn delete(self, k: &K) -> Option<Self>
    where
        K: cmp::Ord,
    {
        match k.cmp(&self.key) {
            cmp::Ordering::Less => Some(Self {
                left: self.left.and_then(|left| left.delete(k).map(Box::new)),
                ..self
            }),
            cmp::Ordering::Equal => match (self.left, self.right) {
                (None, None) => None,
                (None, Some(right)) => Some(*right),
                (Some(left), None) => Some(*left),

                // If we have two children we have to figure out
                // which node to promote. We choose here this node's
                // predecessor. That is, the largest node in this node's
                // left subtree.
                (Some(left_child), right_child) => {
                    let (pred_key, pred_value, new_left) = left_child.delete_largest();
                    Some(Self {
                        left: new_left,
                        right: right_child,
                        key: pred_key,
                        value: pred_value,
                    })
                }
            },
            cmp::Ordering::Greater => Some(Self {
                right: self.right.and_then(|right| right.delete(k).map(Box::new)),
                ..self
            }),
        }
    }
}

/// A Binary Search Tree. This can be used for inserting, finding,
/// and deleting keys and values. Note that this data structure is
/// functional - operations that would modify the tree instead
/// return a new tree.
#[derive(Clone)]
pub struct Tree<K, V>(Option<Node<K, V>>);

impl<K, V> Default for Tree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Tree<K, V> {
    /// Generates a new, empty `Tree`.
    pub fn new() -> Self {
        Self(None)
    }

    /// Returns a new tree that includes a node
    /// containing the given key and value
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::functional::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree = tree.insert(1, 2);
    ///
    /// assert_eq!(tree.find(&1), Some(&2));
    ///
    /// tree = tree.insert(1, 3);
    ///
    /// assert_eq!(tree.find(&1), Some(&3));
    /// ```
    pub fn insert(self, key: K, value: V) -> Self
    where
        K: cmp::Ord,
    {
        match self.0 {
            None => Self(Some(Node::new(key, value))),
            Some(root) => Self(Some(root.insert(key, value))),
        }
    }

    /// Potentially finds the value associated with the given key
    /// in this tree. If no node has the corresponding key, `None`
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::functional::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree = tree.insert(1, 2);
    /// tree = tree.insert(2, 3);
    /// tree = tree.insert(0, 1);
    ///
    /// assert_eq!(tree.find(&1), Some(&2));
    /// assert_eq!(tree.find(&2), Some(&3));
    /// assert_eq!(tree.find(&0), Some(&1));
    /// ```
    pub fn find(&self, k: &K) -> Option<&V>
    where
        K: cmp::Ord,
    {
        self.0.as_ref().and_then(|root| root.find(k))
    }

    /// Returns a new tree without a node with the given key.
    /// If the tree contained a node with the key, it is removed.
    /// If the tree never contained a node with the key, a new
    /// tree is constructed that is identical to the previous.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::functional::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree = tree.insert(1, 2);
    ///
    /// tree = tree.delete(&1);
    ///
    /// assert_eq!(tree.find(&1), None);
    /// ```
    pub fn delete(self, k: &K) -> Self
    where
        K: cmp::Ord,
    {
        Self(self.0.and_then(|root| root.delete(k)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_delete_no_children() {
        let mut tree = Tree::new();
        tree = tree.insert(1, 2);
        tree = tree.insert(2, 3);
        tree = tree.delete(&2);

        assert_eq!(tree.find(&1), Some(&2));
        assert_eq!(tree.find(&2), None);
    }

    #[test]
    fn test_delete_no_left_child() {
        let mut tree = Tree::new();
        tree = tree.insert(1, 2);
        tree = tree.insert(2, 3);
        tree = tree.delete(&1);

        assert_eq!(tree.find(&1), None);
        assert_eq!(tree.find(&2), Some(&3));
    }

    #[test]
    fn test_delete_no_right_child() {
        let mut tree = Tree::new();
        tree = tree.insert(2, 3);
        tree = tree.insert(1, 2);
        tree = tree.delete(&2);

        assert_eq!(tree.find(&1), Some(&2));
        assert_eq!(tree.find(&2), None);
    }

    #[test]
    fn test_delete_two_children_with_no_child() {
        let mut tree = Tree::new();
        tree = tree.insert(2, 3);
        tree = tree.insert(1, 2);
        tree = tree.insert(3, 4);
        tree = tree.delete(&2);

        assert_eq!(tree.find(&1), Some(&2));
        assert_eq!(tree.find(&2), None);
        assert_eq!(tree.find(&3), Some(&4));
    }

    #[test]
    fn test_delete_two_children_with_child() {
        let mut tree = Tree::new();
        tree = tree.insert(2, 3);
        tree = tree.insert(1, 2);
        tree = tree.insert(0, 1);
        tree = tree.insert(3, 4);
        tree = tree.delete(&2);

        assert_eq!(tree.find(&0), Some(&1));
        assert_eq!(tree.find(&1), Some(&2));
        assert_eq!(tree.find(&2), None);
        assert_eq!(tree.find(&3), Some(&4));
    }

    // TODO Test BST invariant
}

#[cfg(test)]
mod quicktests {
    use super::*;
    use crate::test::quick::{Large, Op};
    use std::collections::{HashMap, HashSet};

    fn do_ops<K, V>(ops: &[Op<K, V>], mut bst: Tree<K, V>, map: &mut HashMap<K, V>) -> Tree<K, V>
    where
        K: std::hash::Hash + Eq + Clone + Ord,
        V: std::fmt::Debug + PartialEq + Clone,
    {
        for op in ops {
            match op {
                Op::Insert(k, v) => {
                    bst = bst.insert(k.clone(), v.clone());
                    map.insert(k.clone(), v.clone());
                }
                Op::Remove(k) => {
                    bst = bst.delete(k);
                    map.remove(k);
                }
                Op::CheckGet(k) => {
                    assert_eq!(bst.find(k), map.get(k));
                }
            }
        }

        bst
    }

    fn assert_maps_equivalent<K, V>(bst: &Tree<K, V>, map: &HashMap<K, V>) -> bool
    where
        K: std::hash::Hash + Eq + Clone + Ord,
        V: std::fmt::Debug + PartialEq,
    {
        for key in map.keys() {
            assert_eq!(bst.find(key), map.get(key));
        }
        true
    }

    #[quickcheck]
    fn fuzz_multiple_operations_i8(ops: Large<Vec<Op<i8, i8>>>) -> bool {
        let mut tree = Tree::new();
        let mut map = HashMap::new();

        tree = do_ops(&ops, tree, &mut map);
        assert_maps_equivalent(&tree, &map)
    }

    #[quickcheck]
    fn contains(xs: Vec<i8>) -> bool {
        let mut tree = Tree::new();
        for x in &xs {
            tree = tree.insert(*x, *x);
        }

        xs.iter().all(|x| tree.find(x) == Some(&x))
    }

    #[quickcheck]
    fn contains_not(xs: Vec<i8>, nots: Vec<i8>) -> bool {
        let mut tree = Tree::new();
        for x in &xs {
            tree = tree.insert(*x, *x);
        }
        let added: HashSet<_> = xs.into_iter().collect();
        let nots: HashSet<_> = nots.into_iter().collect();
        let mut nots = nots.difference(&added);

        nots.all(|x| tree.find(x) == None)
    }

    #[quickcheck]
    fn with_deletions(xs: Vec<i8>, deletes: Vec<i8>) -> bool {
        let mut tree = Tree::new();
        for x in &xs {
            tree = tree.insert(*x, *x);
        }
        for delete in &deletes {
            tree = tree.delete(&delete);
        }

        deletes.iter().all(|x| tree.find(x) == None)
    }
}
