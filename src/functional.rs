//! A Functional BST. This is modeled after a BST one would see in
//! a functional language like Haskell. Any operations that one would
//! expect to modify the tree (e.g. `insert` or `delete`) instead return
//! a new tree that reference many of the nodes of the original tree.
//!
//! # Examples
//!
//! ```
//! use bst::functional::Tree;
//!
//! let tree = Tree::new();
//!
//! // Nothing in here yet.
//! assert_eq!(tree.find(&1), None);
//!
//! // This `insert` returns a new tree!
//! let new_tree = tree.insert(1, 2);
//!
//! // The new tree has this new value but the old one doesn't.
//! assert_eq!(new_tree.find(&1), Some(&2));
//! assert_eq!(tree.find(&1), None);
//!
//! // Insert a new value for the same key gives yet another tree.
//! let newer_tree = new_tree.insert(1, 3);
//!
//! // And delete it for good measure.
//! let newest_tree = newer_tree.delete(&1);
//!
//! // All history is preserved.
//! assert_eq!(newest_tree.find(&1), None);
//! assert_eq!(newer_tree.find(&1), Some(&3));
//! assert_eq!(new_tree.find(&1), Some(&2));
//! assert_eq!(tree.find(&1), None);
//! ```

use std::cmp;
use std::rc::Rc;

/// A Binary Search Tree. This can be used for inserting, finding,
/// and deleting keys and values. Note that this data structure is
/// functional - operations that would modify the tree instead
/// return a new tree.
pub enum Tree<K, V> {
    /// A marker for the empty pointer at the bottom of a subtree.
    Leaf,
    /// A `Node` that has a key, value, and two children (which are
    /// both `Tree`s). This enum trivially wraps the [`Node`] struct.
    Node(Node<K, V>),
}

impl<K, V> Default for Tree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Tree<K, V> {
    /// Generates a new, empty `Tree`.
    pub fn new() -> Self {
        Tree::Leaf
    }

    /// Returns a new tree that includes a node
    /// containing the given key and value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::functional::Tree;
    ///
    /// let tree = Tree::new();
    /// let new_tree = tree.insert(1, 2);
    /// let newer_tree = new_tree.insert(1, 3);
    ///
    /// // All history is preserved.
    /// assert_eq!(newer_tree.find(&1), Some(&3));
    /// assert_eq!(new_tree.find(&1), Some(&2));
    /// assert_eq!(tree.find(&1), None);
    /// ```
    pub fn insert(&self, key: K, value: V) -> Self
    where
        K: cmp::Ord,
    {
        match self {
            Tree::Leaf => Tree::Node(Node::new(key, value)),
            Tree::Node(n) => match key.cmp(&n.key) {
                cmp::Ordering::Less => Tree::Node(Node {
                    left: Rc::new(n.left.insert(key, value)),
                    key: Rc::clone(&n.key),
                    right: Rc::clone(&n.right),
                    value: Rc::clone(&n.value),
                }),
                cmp::Ordering::Equal => Tree::Node(Node {
                    value: Rc::new(value),
                    key: Rc::clone(&n.key),
                    left: Rc::clone(&n.left),
                    right: Rc::clone(&n.right),
                }),
                cmp::Ordering::Greater => Tree::Node(Node {
                    right: Rc::new(n.right.insert(key, value)),
                    key: Rc::clone(&n.key),
                    left: Rc::clone(&n.left),
                    value: Rc::clone(&n.value),
                }),
            },
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
    /// let tree = Tree::new();
    /// let tree = tree.insert(1, 2);
    ///
    /// assert_eq!(tree.find(&1), Some(&2));
    /// assert_eq!(tree.find(&42), None);
    /// ```
    pub fn find(&self, k: &K) -> Option<&V>
    where
        K: cmp::Ord,
    {
        match self {
            Tree::Leaf => None,
            Tree::Node(n) => match k.cmp(&n.key) {
                cmp::Ordering::Less => n.left.find(k),
                cmp::Ordering::Equal => Some(&n.value),
                cmp::Ordering::Greater => n.right.find(k),
            },
        }
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
    /// let tree = Tree::new();
    /// let tree = tree.insert(1, 2);
    /// let newer_tree = tree.delete(&1);
    ///
    /// // All history is preserved.
    /// assert_eq!(newer_tree.find(&1), None);
    /// assert_eq!(tree.find(&1), Some(&2));
    /// ```
    pub fn delete(&self, k: &K) -> Self
    where
        K: cmp::Ord,
    {
        match self {
            Tree::Leaf => Tree::Leaf,
            Tree::Node(n) => match k.cmp(&n.key) {
                cmp::Ordering::Less => Tree::Node(Node {
                    left: Rc::new(n.left.delete(k)),
                    key: Rc::clone(&n.key),
                    right: Rc::clone(&n.right),
                    value: Rc::clone(&n.value),
                }),
                cmp::Ordering::Equal => match (n.left.as_ref(), n.right.as_ref()) {
                    (Tree::Leaf, Tree::Leaf) => Tree::Leaf,
                    (Tree::Leaf, Tree::Node(right)) => Tree::Node(right.clone()),
                    (Tree::Node(left), Tree::Leaf) => Tree::Node(left.clone()),

                    // If we have two children we have to figure out
                    // which node to promote. We choose here this node's
                    // predecessor. That is, the largest node in this node's
                    // left subtree.
                    (Tree::Node(left_child), _) => {
                        let (pred_key, pred_val, new_left) = left_child.delete_largest();
                        Tree::Node(Node {
                            left: new_left,
                            right: Rc::clone(&n.right),
                            key: pred_key,
                            value: pred_val,
                        })
                    }
                },
                cmp::Ordering::Greater => Tree::Node(Node {
                    right: Rc::new(n.right.delete(k)),
                    key: Rc::clone(&n.key),
                    left: Rc::clone(&n.left),
                    value: Rc::clone(&n.value),
                }),
            },
        }
    }
}

/// A `Node` has a key that is used for searching/sorting and a value
/// that is associated with that key. It always has two children although
/// those children may be [`Leaf`][Tree::Leaf]s.
pub struct Node<K, V> {
    key: Rc<K>,
    value: Rc<V>,
    left: Rc<Tree<K, V>>,
    right: Rc<Tree<K, V>>,
}

/// Manual implementation of `Clone` so we don't clone references when the generic parameters
/// aren't `Clone` themselves.
///
/// Note the comment on generic structs in
/// [the docs][<https://doc.rust-lang.org/std/clone/trait.Clone.html#derivable>].
impl<K, V> Clone for Node<K, V> {
    fn clone(&self) -> Self {
        Self {
            key: Rc::clone(&self.key),
            left: Rc::clone(&self.left),
            right: Rc::clone(&self.right),
            value: Rc::clone(&self.value),
        }
    }
}

impl<K, V> Node<K, V> {
    /// Construct a new `Node` with the given `key` and `value.
    fn new(key: K, value: V) -> Self {
        Self {
            key: Rc::new(key),
            value: Rc::new(value),
            left: Rc::new(Tree::Leaf),
            right: Rc::new(Tree::Leaf),
        }
    }

    /// Returns the key and value of the largest node and a new subtree without that largest node.
    fn delete_largest(&self) -> (Rc<K>, Rc<V>, Rc<Tree<K, V>>)
    where
        K: cmp::Ord,
    {
        match self.right.as_ref() {
            Tree::Leaf => (
                Rc::clone(&self.key),
                Rc::clone(&self.value),
                Rc::clone(&self.left),
            ),
            Tree::Node(r) => {
                let (key, value, sub) = r.delete_largest();

                (
                    key,
                    value,
                    Rc::new(Tree::Node(Node {
                        right: sub,
                        key: Rc::clone(&self.key),
                        left: Rc::clone(&self.left),
                        value: Rc::clone(&self.value),
                    })),
                )
            }
        }
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
}
