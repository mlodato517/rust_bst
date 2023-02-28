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
        Self::Leaf
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
            Self::Leaf => Self::Node(Node::new(key, value)),
            Self::Node(n) => Self::Node(n.insert(key, value)),
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
            Self::Leaf => None,
            Self::Node(n) => n.find(k),
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
            Self::Leaf => Self::new(),
            Self::Node(n) => n.delete(k).map(Self::Node).unwrap_or_default(),
        }
    }

    /// Gets the height of this tree.
    fn height(&self) -> usize {
        match self {
            Self::Leaf => 0,
            Self::Node(n) => n.height,
        }
    }
}

struct Child<K, V>(Rc<Tree<K, V>>);
impl<K, V> Clone for Child<K, V> {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}
impl<K, V> Child<K, V> {
    fn new() -> Self {
        Self(Rc::new(Tree::new()))
    }

    fn height(&self) -> usize {
        self.0.height()
    }

    fn insert(&self, key: K, value: V) -> Self
    where
        K: cmp::Ord,
    {
        Self(Rc::new(self.0.insert(key, value)))
    }

    fn find(&self, k: &K) -> Option<&V>
    where
        K: cmp::Ord,
    {
        self.0.find(k)
    }

    fn delete(&self, k: &K) -> Self
    where
        K: cmp::Ord,
    {
        Self(Rc::new(self.0.delete(k)))
    }
}

/// A `Node` has a key that is used for searching/sorting and a value
/// that is associated with that key. It always has two children although
/// those children may be [`Leaf`][Tree::Leaf]s.
pub struct Node<K, V> {
    key: Rc<K>,
    value: Rc<V>,
    left: Child<K, V>,
    right: Child<K, V>,

    /// How many levels are in the subtree rooted at this node.
    /// A node with no children has a height of 1.
    height: usize,
}

/// Manual implementation of `Clone` so we don't clone references when the generic parameters
/// aren't `Clone` themselves.
///
/// Note the comment on generic structs in
/// [the docs][<https://doc.rust-lang.org/std/clone/trait.Clone.html#derivable>].
impl<K, V> Clone for Node<K, V> {
    fn clone(&self) -> Self {
        Self {
            height: self.height,
            key: Rc::clone(&self.key),
            left: self.left.clone(),
            right: self.right.clone(),
            value: Rc::clone(&self.value),
        }
    }
}

impl<K, V> Node<K, V> {
    /// Construct a new `Node` with the given `key` and `value.
    fn new(key: K, value: V) -> Self {
        Self {
            height: 1,
            key: Rc::new(key),
            left: Child::new(),
            right: Child::new(),
            value: Rc::new(value),
        }
    }

    /// Create a new Node with the same key/value as this node
    /// but with the given children.
    fn clone_with_children(&self, left_child: Child<K, V>, right_child: Child<K, V>) -> Self {
        let height = left_child.height().max(right_child.height()) + 1;
        Self {
            height,
            key: Rc::clone(&self.key),
            left: left_child,
            right: right_child,
            value: Rc::clone(&self.value),
        }
        .balance()
    }

    fn insert(&self, key: K, value: V) -> Self
    where
        K: cmp::Ord,
    {
        match key.cmp(&self.key) {
            cmp::Ordering::Less => {
                let new_left = self.left.insert(key, value);
                self.clone_with_children(new_left, self.right.clone())
            }
            cmp::Ordering::Equal => Self {
                height: self.height,
                key: Rc::clone(&self.key),
                left: self.left.clone(),
                right: self.right.clone(),
                value: Rc::new(value),
            },
            cmp::Ordering::Greater => {
                let new_right = self.right.insert(key, value);
                self.clone_with_children(self.left.clone(), new_right)
            }
        }
    }

    fn find(&self, k: &K) -> Option<&V>
    where
        K: cmp::Ord,
    {
        match k.cmp(&self.key) {
            cmp::Ordering::Less => self.left.find(k),
            cmp::Ordering::Equal => Some(&self.value),
            cmp::Ordering::Greater => self.right.find(k),
        }
    }

    fn delete(&self, k: &K) -> Option<Self>
    where
        K: cmp::Ord,
    {
        match k.cmp(&self.key) {
            cmp::Ordering::Less => {
                let new_left = self.left.delete(k);
                Some(self.clone_with_children(new_left, self.right.clone()))
            }
            cmp::Ordering::Equal => match (self.left.0.as_ref(), self.right.0.as_ref()) {
                (Tree::Leaf, Tree::Leaf) => None,
                (Tree::Leaf, Tree::Node(right)) => Some(right.clone()),
                (Tree::Node(left), Tree::Leaf) => Some(left.clone()),

                // If we have two children we have to figure out
                // which node to promote. We choose here this node's
                // predecessor. That is, the largest node in this node's
                // left subtree.
                (Tree::Node(left_child), _) => {
                    let (pred_key, pred_val, new_left) = left_child.delete_largest();
                    let height = new_left.height().max(self.right.height()) + 1;
                    Some(
                        Node {
                            height,
                            key: pred_key,
                            left: new_left,
                            right: self.right.clone(),
                            value: pred_val,
                        }
                        .balance(),
                    )
                }
            },
            cmp::Ordering::Greater => {
                let new_right = self.right.delete(k);
                Some(self.clone_with_children(self.left.clone(), new_right))
            }
        }
    }

    /// Returns the key and value of the largest node and a new subtree without that largest node.
    fn delete_largest(&self) -> (Rc<K>, Rc<V>, Child<K, V>)
    where
        K: cmp::Ord,
    {
        match self.right.0.as_ref() {
            Tree::Leaf => (
                Rc::clone(&self.key),
                Rc::clone(&self.value),
                self.left.clone(),
            ),
            Tree::Node(r) => {
                let (key, value, new_right) = r.delete_largest();

                (
                    key,
                    value,
                    Child(Rc::new(Tree::Node(
                        self.clone_with_children(self.left.clone(), new_right),
                    ))),
                )
            }
        }
    }

    /// Returns a new tree by rotating the right child up to become the root. To maintain the AVL
    /// invariant, we lift the right child's left child to be the new left child's right child.
    fn rotate_left(&self) -> Self {
        let old_root = self;
        match &*old_root.right.0 {
            // We can't come into this method without a right child since we only rotate left if
            // the right subtree is taller than the left subtree.
            Tree::Leaf => unreachable!("`balance` saw right child taller than left child."),
            Tree::Node(new_root) => {
                // The old root will be come the left child of the new root. It's left child stays
                // the same and its right child is the left child of the new root (since the new
                // root's left child is changing to be this node).
                let new_left = Tree::Node(Self {
                    height: old_root.left.height().max(new_root.left.height()) + 1,
                    key: Rc::clone(&old_root.key),
                    left: old_root.left.clone(),
                    right: new_root.left.clone(),
                    value: Rc::clone(&old_root.value),
                });

                Self {
                    height: new_root.right.height().max(new_left.height()) + 1,
                    key: Rc::clone(&new_root.key),
                    left: Child(Rc::new(new_left)),
                    right: new_root.right.clone(),
                    value: Rc::clone(&new_root.value),
                }
            }
        }
    }

    /// Returns a new tree by rotating the left child up to become the root. To maintain the AVL
    /// invariant, we lift the left child's right child to be the new right child's left child.
    fn rotate_right(&self) -> Self {
        match self.left.0.as_ref() {
            Tree::Leaf => self.clone(),
            Tree::Node(l) => {
                let new_right = Tree::Node(Self {
                    height: self.right.height().max(l.right.height()) + 1,
                    key: Rc::clone(&self.key),
                    left: l.right.clone(),
                    right: self.right.clone(),
                    value: Rc::clone(&self.value),
                });

                Self {
                    height: l.left.height().max(new_right.height()) + 1,
                    key: Rc::clone(&l.key),
                    left: l.left.clone(),
                    right: Child(Rc::new(new_right)),
                    value: Rc::clone(&l.value),
                }
            }
        }
    }

    /// Balances a tree using the heights of the children.
    ///
    /// **Note** This takes `self` instead of `&self` might not be very functional but it's private,
    /// isn't `mut` and saves us from unnecessary `clone`s when it's already balanced.
    fn balance(self) -> Self {
        let return_node = if self.right.height() > self.left.height() + 1 {
            self.rotate_left()
        } else if self.left.height() > self.right.height() + 1 {
            self.rotate_right()
        } else {
            self
        };

        // In tests, after balancing, assert that we've restored/maintained the AVL invariant.
        if cfg!(test) {
            let right_height = return_node.right.height() as isize;
            let left_height = return_node.left.height() as isize;
            assert!((left_height - right_height).abs() <= 1);
        }
        return_node
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
    fn test_delete_two_children_with_no_grandchildren() {
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
    fn test_delete_two_children_with_grandchild() {
        let mut tree = Tree::new();
        tree = tree.insert(2, 3);
        tree = tree.insert(1, 2);
        tree = tree.insert(3, 4);
        tree = tree.insert(0, 1);
        tree = tree.delete(&2);

        assert_eq!(tree.find(&0), Some(&1));
        assert_eq!(tree.find(&1), Some(&2));
        assert_eq!(tree.find(&2), None);
        assert_eq!(tree.find(&3), Some(&4));
    }

    /// Assert the heights of the root, left child, and right child of a tree.
    macro_rules! assert_heights {
        ($tree:ident, $height:expr, $left_height:expr, $right_height:expr) => {{
            assert_eq!($tree.height(), $height);

            if let Tree::Node(n) = &$tree {
                assert_eq!(n.height, $height);

                assert_eq!(n.right.height(), $right_height);
                assert_eq!(n.left.height(), $left_height);
            }
        }};
    }

    #[test]
    fn test_height() {
        let mut tree = Tree::new();
        assert_eq!(tree.height(), 0);

        tree = tree.insert(1, 1);
        assert_heights!(tree, 1, 0, 0);

        // Insert a value to the right making it taller.
        tree = tree.insert(2, 2);
        assert_heights!(tree, 2, 0, 1);

        // Insert a value to the left not changing the overall height.
        tree = tree.insert(0, 0);
        assert_heights!(tree, 2, 1, 1);

        // Delete that left value to get to the previous heights.
        tree = tree.delete(&0);
        assert_heights!(tree, 2, 0, 1);

        // Put it back and delete the root. It'll be replaced with its left child
        // so we have just the root and a right child.
        tree = tree.insert(0, 0);
        tree = tree.delete(&1);
        assert_heights!(tree, 2, 0, 1);
    }
}
