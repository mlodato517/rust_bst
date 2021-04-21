//! A Functional BST. This is modeled after a BST one would see in
//! a functional language like Haskell. Any operations that one would
//! expect to modify the tree (e.g. `insert` or `delete`) instead return
//! a new tree that reference many of the nodes of the original tree.
//!
//! To avoid copious `Rc`ing, we do not implement a particularly efficient
//! persistent structure - we only allow one tree at a time. Still, most
//! of the algorithms are the same and there are useful lessons to learn!

use std::cmp;

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
        match self {
            Tree::Leaf => Tree::Node(Node::new(key, value)),
            Tree::Node(n) => match key.cmp(&n.key) {
                cmp::Ordering::Less => Tree::Node(Node {
                    left: Box::new(n.left.insert(key, value)),
                    ..n
                }),
                cmp::Ordering::Equal => Tree::Node(Node { value, ..n }),
                cmp::Ordering::Greater => Tree::Node(Node {
                    right: Box::new(n.right.insert(key, value)),
                    ..n
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
    /// let mut tree = Tree::new();
    /// tree = tree.insert(1, 2);
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
        match self {
            Tree::Leaf => self,
            Tree::Node(n) => match k.cmp(&n.key) {
                cmp::Ordering::Less => Tree::Node(Node {
                    left: Box::new(n.left.delete(k)),
                    ..n
                }),
                cmp::Ordering::Equal => match (*n.left, *n.right) {
                    (Tree::Leaf, right_child) => right_child,
                    (left_child, Tree::Leaf) => left_child,

                    // If we have two children we have to figure out
                    // which node to promote. We choose here this node's
                    // predecessor. That is, the largest node in this node's
                    // left subtree.
                    (Tree::Node(left_child), right_child) => {
                        let (pred_key, pred_val, new_left) = left_child.delete_largest();
                        Tree::Node(Node {
                            left: new_left,
                            right: Box::new(right_child), // I really don't want this allocation here
                            key: pred_key,
                            value: pred_val,
                        })
                    }
                },
                cmp::Ordering::Greater => Tree::Node(Node {
                    right: Box::new(n.right.delete(k)),
                    ..n
                }),
            },
        }
    }
}

/// A `Node` tree has a key that is used for searching/sorting and a value
/// that is associated with that key. It always has two children although
/// those children may be [`Leaf`][Tree::Leaf]s.
pub struct Node<K, V> {
    key: K,
    value: V,
    left: Box<Tree<K, V>>,
    right: Box<Tree<K, V>>,
}

impl<K, V> Node<K, V> {
    fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            left: Box::new(Tree::Leaf),
            right: Box::new(Tree::Leaf),
        }
    }

    /// Returns the largest node and a new subtree
    /// without that largest node.
    fn delete_largest(self) -> (K, V, Box<Tree<K, V>>)
    where
        K: cmp::Ord,
    {
        match *self.right {
            Tree::Leaf => (self.key, self.value, self.left),
            Tree::Node(r) => {
                let (key, value, sub) = r.delete_largest();

                (
                    key,
                    value,
                    Box::new(Tree::Node(Node { right: sub, ..self })),
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
