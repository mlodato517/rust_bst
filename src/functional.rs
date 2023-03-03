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
pub struct Tree<K, V> {
    root: Option<Node<K, V>>,
}

impl<K, V> Default for Tree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Tree<K, V> {
    /// Generates a new, empty `Tree`.
    pub fn new() -> Self {
        Self { root: None }
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
        let new_root = match &self.root {
            None => Node::new(key, value),
            Some(root) => root.insert(key, value),
        };

        Self {
            root: Some(new_root),
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
        match &self.root {
            None => None,
            Some(n) => n.find(k),
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
        match &self.root {
            None => Self::new(),
            Some(n) => Self { root: n.delete(k) },
        }
    }
}

struct Child<K, V>(Option<Rc<Node<K, V>>>);
impl<K, V> Clone for Child<K, V> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<K, V> Child<K, V> {
    fn new() -> Self {
        Self(None)
    }

    fn height(&self) -> usize {
        match &self.0 {
            None => 0,
            Some(n) => n.height,
        }
    }

    fn insert(&self, key: K, value: V) -> Self
    where
        K: cmp::Ord,
    {
        let new_node = match &self.0 {
            Some(n) => n.insert(key, value),
            None => Node::new(key, value),
        };
        Self(Some(Rc::new(new_node)))
    }

    fn find(&self, k: &K) -> Option<&V>
    where
        K: cmp::Ord,
    {
        match &self.0 {
            Some(n) => n.find(k),
            None => None,
        }
    }

    fn delete(&self, k: &K) -> Self
    where
        K: cmp::Ord,
    {
        let new_node = match &self.0 {
            Some(n) => n.delete(k).map(Rc::new),
            None => None,
        };
        Self(new_node)
    }
}

/// A `Node` has a key that is used for searching/sorting and a value
/// that is associated with that key. It always has two children although
/// those children may be `Tree::Leaf`s.
struct Node<K, V> {
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
            cmp::Ordering::Equal => match (&self.left.0, &self.right.0) {
                (None, None) => None,
                (None, Some(right)) => Some(Node::clone(right)),
                (Some(left), None) => Some(Node::clone(left)),

                // If we have two children we have to figure out
                // which node to promote. We choose here this node's
                // predecessor. That is, the largest node in this node's
                // left subtree.
                (Some(left_child), _) => {
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
        match &self.right.0 {
            None => (
                Rc::clone(&self.key),
                Rc::clone(&self.value),
                self.left.clone(),
            ),
            Some(r) => {
                let (key, value, new_right) = r.delete_largest();

                (
                    key,
                    value,
                    Child(Some(Rc::new(
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
        match &old_root.right.0 {
            // We can't come into this method without a right child since we only rotate left if
            // the right subtree is taller than the left subtree.
            None => unreachable!("`balance` saw right child taller than left child."),
            Some(new_root) => {
                // The old root will be come the left child of the new root. It's left child stays
                // the same and its right child is the left child of the new root (since the new
                // root's left child is changing to be this node).
                let new_left = Self {
                    height: old_root.left.height().max(new_root.left.height()) + 1,
                    key: Rc::clone(&old_root.key),
                    left: old_root.left.clone(),
                    right: new_root.left.clone(),
                    value: Rc::clone(&old_root.value),
                };

                Self {
                    height: new_root.right.height().max(new_left.height) + 1,
                    key: Rc::clone(&new_root.key),
                    left: Child(Some(Rc::new(new_left))),
                    right: new_root.right.clone(),
                    value: Rc::clone(&new_root.value),
                }
            }
        }
    }

    /// Returns a new tree by rotating the left child up to become the root. To maintain the AVL
    /// invariant, we lift the left child's right child to be the new right child's left child.
    fn rotate_right(&self) -> Self {
        match &self.left.0 {
            None => self.clone(),
            Some(l) => {
                let new_right = Self {
                    height: self.right.height().max(l.right.height()) + 1,
                    key: Rc::clone(&self.key),
                    left: l.right.clone(),
                    right: self.right.clone(),
                    value: Rc::clone(&self.value),
                };

                Self {
                    height: l.left.height().max(new_right.height) + 1,
                    key: Rc::clone(&l.key),
                    left: l.left.clone(),
                    right: Child(Some(Rc::new(new_right))),
                    value: Rc::clone(&l.value),
                }
            }
        }
    }

    /// Perform a [double rotation][wikipedia] to rebalance this node. This right-left double
    /// rotation involves rotating the right child right and then rotating the root left.
    ///
    /// ## Panics
    ///
    /// This panics if called on a node without a right child (i.e. a node that shouldn't be
    /// right-left rotated).
    ///
    /// [wikipedia]: https://en.wikipedia.org/wiki/AVL_tree#Double_rotation
    fn rotate_right_left(&self) -> Self {
        let new_right = {
            let right = self.right.0.as_ref();
            let right = right.expect("right-left rotating node should have a right child");
            right.rotate_right()
        };

        // Careful with `clone_with_children` here - that calls `balance` which calls this.
        // It's not an infinite loop or anything, it's just wasteful due to recalculation.
        let x_prime = Self {
            key: Rc::clone(&self.key),
            value: Rc::clone(&self.value),
            height: self.height,
            left: self.left.clone(),
            right: Child(Some(Rc::new(new_right))),
        };
        x_prime.rotate_left()
    }

    /// Perform a [double rotation][wikipedia] to rebalance this node. This left-right double
    /// rotation involves rotating the left child left and then rotating the root right.
    ///
    /// ## Panics
    ///
    /// This panics if called on a node without a left child (i.e. a node that shouldn't be
    /// left-right rotated).
    ///
    /// [wikipedia]: https://en.wikipedia.org/wiki/AVL_tree#Double_rotation
    fn rotate_left_right(&self) -> Self {
        let new_left = {
            let left = self.left.0.as_ref();
            let left = left.expect("left-right rotating node should have a left child");
            left.rotate_left()
        };

        // Careful with `clone_with_children` here - that calls `balance` which calls this.
        // It's not an infinite loop or anything, it's just wasteful due to recalculation.
        let x_prime = Self {
            key: Rc::clone(&self.key),
            value: Rc::clone(&self.value),
            height: self.height,
            left: Child(Some(Rc::new(new_left))),
            right: self.right.clone(),
        };
        x_prime.rotate_right()
    }

    /// Balances a tree using the heights of the children.
    ///
    /// **Note** This takes `self` instead of `&self` might not be very functional but it's private,
    /// isn't `mut` and saves us from unnecessary `clone`s when it's already balanced.
    fn balance(self) -> Self {
        // TODO there is probably wasted effort here - we have information based on _where this is
        // called_ that changes what checks we should make. For instance, if we just inserted into
        // our left tree, it's not valuable to check if the right subtree is too tall.
        //
        // See https://en.wikipedia.org/wiki/AVL_tree#Rebalancing for terminology/logic.
        let return_node = match (&self.left.0, &self.right.0) {
            (Some(left), _) if left.height > self.right.height() + 1 => {
                let balance_factor = left.right.height() as isize - left.left.height() as isize;
                if balance_factor <= 0 {
                    self.rotate_right()
                } else {
                    self.rotate_left_right()
                }
            }
            (_, Some(right)) if right.height > self.left.height() + 1 => {
                let balance_factor = right.right.height() as isize - right.left.height() as isize;
                if balance_factor >= 0 {
                    self.rotate_left()
                } else {
                    self.rotate_right_left()
                }
            }
            _ => self,
        };

        if cfg!(debug_assertions) {
            // Assert that we've restored/maintained the AVL invariant.
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
            assert_eq!($tree.root.as_ref().map_or(0, |root| root.height), $height);

            if let Some(n) = &$tree.root {
                assert_eq!(n.height, $height);

                assert_eq!(n.right.height(), $right_height);
                assert_eq!(n.left.height(), $left_height);
            }
        }};
    }

    #[test]
    fn test_height() {
        let mut tree = Tree::new();
        assert_heights!(tree, 0, 0, 0);

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

    #[test]
    fn test_left_right_rebalance() {
        let mut tree = Tree::new();

        tree = tree.insert(0, 0);
        tree = tree.insert(-2, -2);
        tree = tree.insert(-1, -1);

        assert_heights!(tree, 2, 1, 1);
    }

    #[test]
    fn test_right_left_rebalance() {
        let mut tree = Tree::new();

        tree = tree.insert(0, 0);
        tree = tree.insert(2, 2);
        tree = tree.insert(1, 1);

        assert_heights!(tree, 2, 1, 1);
    }
}

#[cfg(test)]
mod quicktests {
    use std::collections::{HashMap, HashSet};

    use super::*;
    use crate::test::quick::Op;

    /// Applies a set of operations to a tree and a hashmap.
    /// This way we can ensure that after a random smattering of inserts
    /// and deletes we have the same set of keys in the map.
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
            }
        }

        bst
    }

    quickcheck::quickcheck! {
        fn fuzz_multiple_operations_i8(ops: Vec<Op<i8, i8>>) -> bool {
            let mut tree = Tree::new();
            let mut map = HashMap::new();

            tree = do_ops(&ops, tree, &mut map);
            map.keys().all(|key| tree.find(key) == map.get(key))
        }
    }

    quickcheck::quickcheck! {
        fn contains(xs: Vec<i8>) -> bool {
            let mut tree = Tree::new();
            for x in &xs {
                tree = tree.insert(*x, *x);
            }

            xs.iter().all(|x| tree.find(x) == Some(x))
        }
    }

    quickcheck::quickcheck! {
        fn contains_not(xs: Vec<i8>, nots: Vec<i8>) -> bool {
            let mut tree = Tree::new();
            for x in &xs {
                tree = tree.insert(*x, *x);
            }
            let added: HashSet<_> = xs.into_iter().collect();
            let nots: HashSet<_> = nots.into_iter().collect();
            let mut nots = nots.difference(&added);

            nots.all(|x| tree.find(x).is_none())
        }
    }

    quickcheck::quickcheck! {
        fn with_deletions(xs: Vec<i8>, deletes: Vec<i8>) -> bool {
            let mut tree = Tree::new();
            for x in &xs {
                tree = tree.insert(*x, *x);
            }
            for delete in &deletes {
                tree = tree.delete(delete);
            }

            let mut still_present = xs;
            for delete in &deletes {
                // We may have inserted the same value multiple times - delete each one.
                while let Some(pos) = still_present.iter().position(|x| x == delete) {
                    still_present.swap_remove(pos);
                }
            }

            deletes.iter().all(|x| tree.find(x).is_none())
                && still_present.iter().all(|x| tree.find(x).is_some())
        }
    }
}
