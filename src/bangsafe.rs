//! An unsafe BST. Similar to the standard library except keeping two children per parent instead
//! of an array based `BTree`.
//!
//! # Examples
//!
//! ```
//! use bst::bangsafe::Tree;
//!
//! let mut tree = Tree::new();
//!
//! // Nothing in here yet.
//! assert_eq!(tree.find(&1), None);
//!
//! tree.insert(1, 2);
//! assert_eq!(tree.find(&1), Some(&2));
//!
//! // Inserting a new value for the same key overwrites the value.
//! tree.insert(1, 3);
//! assert_eq!(tree.find(&1), Some(&3));
//!
//! // Deleting a node returns its value.
//! let deleted_value = tree.delete(&1);
//!
//! assert_eq!(deleted_value, Some(3));
//! assert_eq!(tree.find(&1), None);
//! ```

use std::cmp::Ordering;
use std::fmt;
use std::mem::ManuallyDrop;
use std::ptr::NonNull;

/// Marker value for a `Node`'s height when its value has been removed during deletion. This is
/// used to ensure that the value isn't re-dropped in `Node::drop`.
const VALUE_REMOVED: usize = 0;

/// A self-balancing Binary Search Tree (specifically, an AVL tree). This can be used for
/// inserting, finding, and deleting keys and values.
pub struct Tree<K, V> {
    // This is a pointer instead of a `Node` so that it can be moved around with the `Tree` without
    // the children's parent pointers breaking.
    root: Option<NonNull<Node<K, V>>>,
}

impl<K, V> Default for Tree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Drop for Tree<K, V> {
    // TODO stack based drop
    fn drop(&mut self) {
        if let Some(mut root) = self.root.take() {
            // SAFETY: We own the root we're dropping so this won't be called twice. The root was
            // initially allocated using `Box::new` (in `Node::new_boxed`) so this should be well
            // aligned, etc.
            unsafe { drop(Box::from_raw(root.as_mut())) };
        }
    }
}

impl<K, V> fmt::Debug for Tree<K, V>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    // TODO stack based Debug
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Tree").field("root", &self.root()).finish()
    }
}

impl<K, V> Tree<K, V> {
    /// Generate a new, empty `Tree`.
    pub fn new() -> Self {
        Self { root: None }
    }

    /// Potentially finds the value associated with the given key in this tree. If no node has the
    /// corresponding key, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::bangsafe::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree.insert(1, 2);
    ///
    /// assert_eq!(tree.find(&1), Some(&2));
    /// assert_eq!(tree.find(&42), None);
    /// ```
    pub fn find(&self, key: &K) -> Option<&V>
    where
        K: Ord,
    {
        self.root().and_then(|n| n.find(key))
    }

    /// Inserts the given value into the tree stored at the given key. Inserting a new value for an
    /// existing key overwites its value.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::bangsafe::Tree;
    ///
    /// let mut tree = Tree::new();
    ///
    /// tree.insert(1, 2);
    /// assert_eq!(tree.find(&1), Some(&2));
    ///
    /// tree.insert(1, 3);
    /// assert_eq!(tree.find(&1), Some(&3));
    /// ```
    pub fn insert(&mut self, key: K, value: V)
    where
        K: Ord,
    {
        match self.root_mut() {
            Some(root) => root.insert(key, value),
            None => self.root = Some(NonNull::from(Box::leak(Node::new_boxed(key, value)))),
        }
    }

    /// Deletes the node containing the given key from the tree and returns its value. If the tree
    /// does not contain a node with the key, nothing happens.
    ///
    /// # Examples
    ///
    /// ```
    /// use bst::bangsafe::Tree;
    ///
    /// let mut tree = Tree::new();
    /// tree.insert(1, 2);
    /// let inserted_value = tree.delete(&1);
    ///
    /// assert_eq!(inserted_value, Some(2));
    /// assert_eq!(tree.find(&1), None);
    /// ```
    pub fn delete(&mut self, key: &K) -> Option<V>
    where
        K: Ord,
    {
        match self.root_mut().map(|root| (root.delete(key), root)) {
            Some((DeleteResult::DeleteSelf, _)) => {
                let deleted = self.root.take().expect("Deleting root implies root");
                // SAFETY: Getting `DeleteSelf` here means we deleted the root and it had no
                // children. This means nothing references it except this `Tree`. We just called
                // `self.root.take()` so now the `Tree` doesn't reference it either. So nothing
                // could dereference the value after this.
                unsafe { Some(Node::take_value(deleted)) }
            }
            Some((DeleteResult::DeletedChild(value), root)) => {
                root.balance();
                Some(value)
            }
            None | Some((DeleteResult::NotFound, _)) => None,
        }
    }

    fn root(&self) -> Option<&Node<K, V>> {
        // SAFETY: If the root is not `None` then it is a valid `Node`. Because we take `&self`
        // here, there can be no aliasing with `self.root_mut()`. There can only be aliasing with
        // `self.root.unwrap().as_mut()`. This code would be unsafe so it'd be the caller's
        // responsibility to ensure there is no existing borrow of `root`.
        //
        // This isn't the sexiest guarantee but it feels similar to `ManuallyDrop::drop`. It's
        // unsafe to drop it because _later_ it could be dereferenced (or there is a current
        // reference).
        unsafe { self.root.as_ref().map(|root| root.as_ref()) }
    }

    fn root_mut(&mut self) -> Option<&mut Node<K, V>> {
        // SAFETY: If the root is not `None` then it is a valid `Node`. Because we take `&mut self`
        // here, there can be no aliasing with `self.root/root_mut()`. There can only be aliasing
        // with `self.root.unwrap().as_mut/ref()`. This code would be unsafe so it'd be the
        // caller's responsibility to ensure there is no existing borrow of `root`.
        //
        // This isn't the sexiest guarantee but it feels similar to `ManuallyDrop::drop`. It's
        // unsafe to drop it because _later_ it could be dereferenced (or there is a current
        // reference).
        unsafe { self.root.as_mut().map(|root| root.as_mut()) }
    }
}

enum DeleteResult<V> {
    /// The key wasn't found so nothing was deleted.
    NotFound,
    /// The Node returning this is being deleted and has no children to replace itself with. The
    /// parent who receives this should drop the child and remove its value using
    /// [`Node::take_value`].
    DeleteSelf,
    /// A child node was deleted yielding the value `V` which can be returned to the parent.
    DeletedChild(V),
}

struct Node<K, V> {
    key: K,
    value: ManuallyDrop<V>,
    left: Option<NonNull<Node<K, V>>>,
    right: Option<NonNull<Node<K, V>>>,
    height: usize,
    parent: Option<NonNull<Node<K, V>>>,
}

impl<K, V> Drop for Node<K, V> {
    // TODO Stack based drop
    fn drop(&mut self) {
        // SAFETY: Dropping a node doesn't drop its parent and we are the only owners of these
        // children so we won't drop them twice. They were initially allocated using `Box::new` (in
        // `Node::new_boxed`) so they should be well aligned, etc.
        unsafe {
            if let Some(mut left) = self.left.take() {
                drop(Box::from_raw(left.as_mut()));
            }
            if let Some(mut right) = self.right.take() {
                drop(Box::from_raw(right.as_mut()));
            }
        }
        // Check if the value has already been removed by `Node::take_value`.
        if self.height != VALUE_REMOVED {
            // SAFETY: We're dropping `self` so no one can use this `ManuallyDrop` to access the
            // inner value after dropping. Because we don't have a height of `VALUE_REMOVED`, this
            // value hasn't been taken yet so we're not dropping it twice.
            unsafe { ManuallyDrop::drop(&mut self.value) };
        }
    }
}

impl<K, V> fmt::Debug for Node<K, V>
where
    K: fmt::Debug,
    V: fmt::Debug,
{
    // TODO stack based Debug
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Node")
            .field("key", &self.key)
            .field("height", &self.height)
            .field("value", &self.value)
            .field("left", &self.left())
            .field("right", &self.right())
            .finish()
    }
}

impl<K, V> Node<K, V> {
    fn new_boxed(key: K, value: V) -> Box<Self> {
        Box::new(Node {
            height: 1,
            key,
            left: None,
            parent: None,
            right: None,
            value: ManuallyDrop::new(value),
        })
    }

    fn left(&self) -> Option<&Self> {
        // SAFETY: See the comment on `Tree::root`.
        unsafe { self.left.as_ref().map(|left| left.as_ref()) }
    }

    fn right(&self) -> Option<&Self> {
        // SAFETY: See the comment on `Tree::root`.
        unsafe { self.right.as_ref().map(|right| right.as_ref()) }
    }

    fn left_mut(&mut self) -> Option<&mut Self> {
        // SAFETY: See the comment on `Tree::root_mut`.
        unsafe { self.left.as_mut().map(|left| left.as_mut()) }
    }

    fn right_mut(&mut self) -> Option<&mut Self> {
        // SAFETY: See the comment on `Tree::root_mut`.
        unsafe { self.right.as_mut().map(|right| right.as_mut()) }
    }

    fn fix_left_child_parent(&mut self) {
        let self_ptr = NonNull::from(&*self);
        if let Some(left) = self.left_mut() {
            left.parent = Some(self_ptr);
        }
    }

    fn fix_right_child_parent(&mut self) {
        let self_ptr = NonNull::from(&*self);
        if let Some(right) = self.right_mut() {
            right.parent = Some(self_ptr);
        }
    }

    fn find(&self, key: &K) -> Option<&V>
    where
        K: Ord,
    {
        match key.cmp(&self.key) {
            Ordering::Less => self.left().and_then(|n| n.find(key)),
            Ordering::Equal => Some(&self.value),
            Ordering::Greater => self.right().and_then(|n| n.find(key)),
        }
    }

    fn insert(&mut self, key: K, value: V)
    where
        K: Ord,
    {
        match key.cmp(&self.key) {
            Ordering::Less => match self.left_mut() {
                Some(left) => {
                    left.insert(key, value);
                    self.balance();
                }
                None => {
                    self.left = Some(NonNull::from(Box::leak(Self::new_boxed(key, value))));
                    // Because `self` is an AVL tree before this insert, either:
                    //   1. `self.right` was empty and `self` had height 1
                    //   2. `self.right` was non-empty and `self` had height 2
                    //
                    // In either case, `self` now has a height of 2.
                    self.height = 2;
                }
            },
            Ordering::Equal => {
                let old_value = std::mem::replace(&mut self.value, ManuallyDrop::new(value));
                ManuallyDrop::into_inner(old_value);
            }
            Ordering::Greater => match self.right_mut() {
                Some(right) => {
                    right.insert(key, value);
                    self.balance();
                }
                None => {
                    self.right = Some(NonNull::from(Box::leak(Self::new_boxed(key, value))));
                    // See the comment in the same case for `Ordering:::Less`
                    self.height = 2;
                }
            },
        }

        if cfg!(debug_assertions) {
            if let Some(left) = self.left() {
                assert!(self.key > left.key);
            }
            if let Some(right) = self.right() {
                assert!(self.key < right.key);
            }
        }
    }

    /// Rotate self to the right. This moves the left child up vertically and self down vertically.
    /// Used to rebalance the tree when the left child is too tall. As such, it must only be called
    /// when there _is_ a left child.
    ///
    /// ## Panics
    ///
    /// When called on a node without a left child.
    ///
    /// # Diagram
    ///
    /// Roughly speaking, we want to perform this transformation:
    ///
    /// ```text
    ///    Option<parent>            Option<parent>
    ///      /                         /
    ///   old_root (i.e. "self")    new_root
    ///    /     \                  /     \
    /// new_root  z     rotate ->  x    old_root
    ///  / \                               /  \
    /// x   y                             y    z
    /// ```
    ///
    /// This looks like:
    /// 1. `parent.left = new_root; new_root.parent = parent;`
    /// 2. `old_root.left = new_root.right; old_root.left.parent = old_root;`
    /// 3. `old_root.parent = new_root; new_root.right = old_root;`
    ///
    /// One issue here is that, if `self` is the root of the entire tree (i.e. there is no parent),
    /// then we can't communicate to the `Tree` that its root changed. Instead, we have to modify
    /// `old_root` directly via something like `std::mem::swap(old_root, new_root)`. That leaves us
    /// in an incredibly confusing situation where a bunch of children pointers don't match up with
    /// `parent` pointers:
    ///
    /// ```text
    ///    Option<parent>          Option<parent>
    ///      /                      /       ^
    ///   old_root                 v        |
    ///    /     \         ->   new_root old_root
    /// new_root  z              / ^ \    ^ ^\
    ///  / \                    /  |  v  / /  \
    /// x   y                   |  |  y-/ /    |
    ///                         |  |     /     |
    ///                         v  |    /      v
    ///                         x------/       z
    ///                             \---------/
    /// ```
    ///
    /// Note here that `new_root.parent = new_root` and `old_root.left = old_root`. Those are self
    /// referential which isn't easy to draw...
    ///
    /// Looking at our original picture, we need to swap the two root parents:
    ///
    /// ```text
    /// std::mem::swap(new_root.parent, old_root.parent);
    /// ```
    ///
    /// ```text
    ///    Option<parent>            Option<parent>
    ///     /       ^                 /   /---
    ///    v        |                /   v    \
    /// new_root old_root    ->   new_root old_root
    ///  / ^ \    ^ ^\             / ^ \    ^ ^\
    /// /  |  v  / /  \           /  |  v  / /  \
    /// |  |  y-/ /    |          |  |  y-/ /    |
    /// |  |     /     |          |  |     /     |
    /// v  |    /      v          v  |    /      v
    /// x------/       z          x------/       z
    ///     \---------/               \---------/
    /// ```
    ///
    /// Next, we'll fix one pair of children/parents. We'll start with `old_root.left` and
    /// `new_root.right`:
    ///
    /// ```text
    /// old_root.left = new_root.right;
    /// new_root.right = old_root;
    /// ```
    ///
    /// ```text
    ///    Option<parent            Option<parent
    ///     /   /---                 /
    ///    /   v    \            new_root
    /// new_root old_root   ->    / ^  \
    ///  / ^ \    ^ ^\           /  | old_root
    /// /  |  v  / /  \          |  |  / ^ \
    /// |  |  y-/ /    |         |  | y  |  |
    /// |  |     /     |         v  |    /  |
    /// v  |    /      v         x------/   v
    /// x------/       z             \------z
    ///     \---------/
    /// ```
    ///
    /// Finally, we fix the other pair of children/parents (i.e. `old_root.right` and
    /// `new_root.left`):
    ///
    /// ```text
    /// old_root.right.parent = old_root;
    /// new_root.left.parent = new_root;
    /// ```
    ///
    /// ```text
    ///    Option<parent           Option<parent>
    ///     /                        /
    /// new_root                  new_root
    ///  / ^  \             ->    /     \
    /// /  | old_root            x    old_root
    /// |  |  / ^ \                      /  \
    /// |  | y  |  |                    y    z
    /// v  |    /  |
    /// x------/   v
    ///     \------z
    /// ```
    fn rotate_right(&mut self)
    where
        K: Ord,
    {
        // TODO Optimize - use const generics to make this generic over if we're the root. If we
        // are (and we probably rarely will be), we have to do the below. If we aren't, we can just
        // swap some pointers around.

        // SAFETY: The only code dereferencing the node behind `self.left` is code called directly
        // on `old_root` so there is no aliasing.
        let old_root = unsafe {
            self.left
                .expect("Rotating right implies a left child")
                .as_mut()
        };
        let new_root = &mut *self;
        std::mem::swap(new_root, old_root);
        std::mem::swap(&mut new_root.parent, &mut old_root.parent);

        // Due to stacked borrows, we must make all modifications to `old_parent` first before
        // going back to `new_parent`
        old_root.left = new_root.right;
        old_root.fix_right_child_parent();
        old_root.fix_height();

        new_root.right = Some(old_root.into());
        new_root.fix_left_child_parent();
        new_root.fix_height();
    }

    /// Perform a double left-right rotation to maintain the AVL property. See [the Wikipedia
    /// article][wiki] for more details.
    ///
    /// ## Panics
    ///
    /// Panics if called on a `Node` with no left child.
    ///
    /// [wiki]: https://en.wikipedia.org/wiki/AVL_tree#Double_rotation
    fn rotate_left_right(&mut self)
    where
        K: Ord,
    {
        self.left_mut()
            .expect("Rotating left-right requires left child")
            .rotate_left();
        self.rotate_right();
    }

    /// Rotate self to the left. This moves the right child up vertically and self down vertically.
    /// Used to rebalance the tree when the right child is too tall. As such, it must only be called
    /// when there _is_ a right child.
    ///
    /// For more information, see the documentation on [`Node::rotate_right`].
    ///
    /// ## Panics
    ///
    /// When called on a node without a right child.
    fn rotate_left(&mut self)
    where
        K: Ord,
    {
        // TODO Optimize - use const generics to make this generic over if we're the root. If we
        // are (and we probably rarely will be), we have to do the below. If we aren't, we can just
        // swap some pointers around.

        // SAFETY: The only code dereferencing the node behind `self.right` is code called directly
        // on `old_root` so there is no aliasing.
        let old_root = unsafe {
            self.right
                .expect("Rotating left implies a right child")
                .as_mut()
        };
        let new_root = &mut *self;
        std::mem::swap(new_root, old_root);
        std::mem::swap(&mut new_root.parent, &mut old_root.parent);

        // Due to stacked borrows we must make all modifications to `old_parent` first before going
        // back to `new_parent`
        old_root.right = new_root.left;
        old_root.fix_left_child_parent();
        old_root.fix_height();

        new_root.left = Some(old_root.into());
        new_root.fix_right_child_parent();
        new_root.fix_height();
    }

    /// Perform a double right-left rotation to maintain the AVL property. See [the Wikipedia
    /// article][wiki] for more details.
    ///
    /// ## Panics
    ///
    /// Panics if called on a `Node` with no right child.
    ///
    /// [wiki]: https://en.wikipedia.org/wiki/AVL_tree#Double_rotation
    fn rotate_right_left(&mut self)
    where
        K: Ord,
    {
        self.right_mut()
            .expect("Rotating right-left requires right child")
            .rotate_right();
        self.rotate_left();
    }

    fn balance(&mut self)
    where
        K: Ord,
    {
        // TODO this is probably inefficient - inlining this probably allows us to avoid checks
        // (e.g. if we just inserted into the right child, we don't need to check if the left node
        // is taller) but this currently matches the immutable tree so it's a better performance
        // comparison.
        //
        // TODO there are lots of duplicate `is_null()` and `match Option<>` branches in here.
        //
        // See https://en.wikipedia.org/wiki/AVL_tree#Rebalancing for terminology.
        self.fix_height();
        match (self.balance_factor(), self.left(), self.right()) {
            (-2, Some(left), _) => match left.balance_factor() {
                n if n <= 0 => self.rotate_right(),
                _ => self.rotate_left_right(),
            },
            (2, _, Some(right)) => match right.balance_factor() {
                n if n >= 0 => self.rotate_left(),
                _ => self.rotate_right_left(),
            },
            _ => {}
        }

        if cfg!(debug_assertions) {
            let left_height = self.left().map_or(0, |n| n.height);
            let right_height = self.right().map_or(0, |n| n.height);
            assert_eq!(self.height, left_height.max(right_height) + 1);
            assert!(left_height.abs_diff(right_height) <= 1);
        }
    }

    /// Adjusts the height of `self` to be the max of its children's heights + 1.
    fn fix_height(&mut self) {
        let left_height = self.left().map_or(0, |n| n.height);
        let right_height = self.right().map_or(0, |n| n.height);

        // These checks allow us to use `self.height == VALUE_REMOVED` as a check for "do we
        // need to drop the value?". Also, having a tree this high means you have roughly
        // 2**usize::MAX nodes which is insane.
        assert!(left_height < usize::MAX);
        assert!(right_height < usize::MAX);

        self.height = left_height.max(right_height) + 1;
    }

    /// The difference in height between the right and left subtrees. See [the Wikipedia
    /// page][wiki] for more details.
    ///
    /// [wiki]: https://en.wikipedia.org/wiki/AVL_tree#Balance_factor
    fn balance_factor(&self) -> isize {
        let right_height = self.right().map_or(0, |n| n.height);
        let left_height = self.left().map_or(0, |n| n.height);
        right_height as isize - left_height as isize
    }

    /// Deletes the node with the given `key` from this subtree. See the documentation on
    /// [`DeleteResult`] to see what the various return values mean.
    fn delete(&mut self, key: &K) -> DeleteResult<V>
    where
        K: Ord,
    {
        let result = match key.cmp(&self.key) {
            Ordering::Less => match self.left_mut().map(|n| n.delete(key)) {
                Some(DeleteResult::DeleteSelf) => {
                    let deleted_left = self.left.take().expect("Deleting left => left");
                    // SAFETY: Getting `DeleteSelf` here means we deleted the left child and it had
                    // no children. This means nothing references it except this `Node`. We just
                    // called `self.left.take()` so now this `Node` doesn't reference it either. So
                    // nothing could dereference the value after this.
                    unsafe { DeleteResult::DeletedChild(Node::take_value(deleted_left)) }
                }
                Some(delete_result) => delete_result,
                None => DeleteResult::NotFound,
            },
            Ordering::Equal => match (self.left.take(), self.right.take()) {
                // We'll let our parent drop us and take our value
                (None, None) => DeleteResult::DeleteSelf,
                (None, Some(mut to_delete)) => {
                    // TODO Optimize - use const generics to make this generic over if we're the
                    // root. If we are (and we probably rarely will be), we have to do the below.
                    // If we aren't, we can just swap some pointers around.

                    // SAFETY: No other pointers are dereferenced during `deleted`'s lifetime. The
                    // next dereference is in `Node::take_value` which happens after.
                    unsafe {
                        let deleted = to_delete.as_mut();
                        std::mem::swap(self, deleted);

                        // NB we don't have to fix child pointers here because of the below note on
                        // `self.right` not having children.
                        self.parent = deleted.parent;
                    }

                    // SAFETY: Because we used `std::mem::swap`, we're deleting `self'`s right
                    // child. Because `self` is an AVL node and `self.left` is empty, `self.right`
                    // had no children. So nothing references `to_delete` except this node. We just
                    // called `self.right.take()` so now this `Node` doesn't reference it either.
                    // So nothing could dereference the value after this.
                    unsafe { DeleteResult::DeletedChild(Node::take_value(to_delete)) }
                }
                (Some(mut to_delete), None) => {
                    // SAFETY: No other pointers are dereferenced during `deleted`'s lifetime. The
                    // next dereference is in `Node::take_value` which happens after.
                    unsafe {
                        let deleted = to_delete.as_mut();
                        std::mem::swap(self, deleted);

                        // NB we don't have to fix child pointers here because of the below note on
                        // `self.left` not having children.
                        self.parent = deleted.parent;
                    }

                    // SAFETY: Because we used `std::mem::swap`, we're deleting `self'`s left
                    // child. Because `self` is an AVL node and `self.right` is empty, `self.left`
                    // had no children. So nothing references `to_delete` except this node. We just
                    // called `self.left.take()` so now this `Node` doesn't reference it either. So
                    // nothing could dereference the value after this.
                    unsafe { DeleteResult::DeletedChild(Node::take_value(to_delete)) }
                }
                (Some(mut left_node), Some(right)) => {
                    // SAFETY: This reference only lives during `delete_largest` which only
                    // recurses down and never dereferences a parent so this isn't aliased.
                    match unsafe { left_node.as_mut().delete_largest() } {
                        DeleteResult::DeletedChild(mut to_delete) => {
                            // SAFETY: No other pointers are dereferenced during `deleted`'s
                            // lifetime. The next dereference is in `Node::take_value` which
                            // happens after.
                            unsafe {
                                let deleted = to_delete.as_mut();
                                std::mem::swap(self, deleted);

                                self.parent = deleted.parent;
                                self.right = Some(right);
                                self.left = Some(left_node);
                            }

                            // SAFETY: Because we used `std::mem::swap`, we're deleting `self'`s
                            // predecessor. By definition it didn't have any right children. It was
                            // only referenced by its parent and potentially a left child.
                            // `delete_largest` broke those links so now it's not referenced by
                            // anything meaning its value can't be referenced after this.
                            unsafe { DeleteResult::DeletedChild(Node::take_value(to_delete)) }
                        }
                        DeleteResult::DeleteSelf => {
                            let mut to_delete = left_node;
                            // SAFETY: No other pointers are dereferenced during `deleted`'s
                            // lifetime. The next dereference is in `fix_left_child_parent` which
                            // happens after.
                            unsafe {
                                let deleted = to_delete.as_mut();
                                std::mem::swap(self, deleted);

                                self.parent = deleted.parent;
                                self.right = Some(right);
                            }
                            self.fix_left_child_parent();

                            // SAFETY: Because we used `std::mem::swap`, we're deleting `self'`s
                            // left child. Because we got `DeleteSelf`, it had no right children.
                            // It was only referenced by its parent and potentially a left child.
                            // `swap` broke the parent link and `fix_left_child_parent` broke the
                            // child link so now it's not referenced by anything meaning its value
                            // can't be referenced after this.
                            unsafe { DeleteResult::DeletedChild(Node::take_value(to_delete)) }
                        }
                        DeleteResult::NotFound => {
                            panic!("Predecessor not found but self.left was not null")
                        }
                    }
                }
            },
            Ordering::Greater => match self.right_mut().map(|n| n.delete(key)) {
                Some(DeleteResult::DeleteSelf) => {
                    let deleted_right = self.right.take().expect("Deleting implies existence");
                    // SAFETY: Getting `DeleteSelf` here means we deleted the right child and it
                    // had no children. This means nothing references it except this `Node`. We
                    // just called `self.right.take()` so now this `Node` doesn't reference it
                    // either. So nothing could dereference the value after this.
                    unsafe { DeleteResult::DeletedChild(Node::take_value(deleted_right)) }
                }
                Some(delete_result) => delete_result,
                None => DeleteResult::NotFound,
            },
        };

        // TODO Can probably call more surgically
        if !matches!(result, DeleteResult::NotFound) {
            self.balance();
        }

        result
    }

    /// # Safety
    ///
    /// The caller must ensure that the value of the passed node is never referenced.
    unsafe fn take_value(mut node: NonNull<Node<K, V>>) -> V {
        let mut node: Node<K, V> = *Box::from_raw(node.as_mut());
        node.height = VALUE_REMOVED;

        ManuallyDrop::take(&mut node.value)
    }

    /// Deletes the largest node in the tree by recursing to the right until there is no right
    /// child.
    fn delete_largest(&mut self) -> DeleteResult<NonNull<Self>>
    where
        K: Ord,
    {
        let Some(right) = self.right.as_mut() else {
            return DeleteResult::DeleteSelf;
        };
        // SAFETY: The only other dereferences after this are:
        //   1. `self.fix_right_child_parent`
        //   2. `self.balance`
        //
        // Because both of these occur after setting `self.right = right.left.take()`, `self` no
        // longer has a pointer to `right` and can't make an aliasing reference.
        let right = unsafe { right.as_mut() };
        match right.delete_largest() {
            DeleteResult::DeleteSelf => {
                self.right = right.left.take();
                self.fix_right_child_parent();
                self.balance();
                DeleteResult::DeletedChild(right.into())
            }
            result @ DeleteResult::DeletedChild(_) => {
                self.balance();
                result
            }
            DeleteResult::NotFound => panic!("No largest node in tree with right child!"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Assert the heights of the root, left child, and right child of a tree.
    macro_rules! assert_heights {
        ($tree:ident, $height:expr, $left_height:expr, $right_height:expr) => {{
            match $tree.root() {
                Some(n) => {
                    assert_eq!(n.height, $height);

                    let left_height = n.left().map_or(0, |n| n.height);
                    let right_height = n.right().map_or(0, |n| n.height);
                    assert_eq!(right_height, $right_height);
                    assert_eq!(left_height, $left_height);
                }
                None => assert_eq!(0, $height),
            }
        }};
    }

    #[test]
    fn always_adding_left() {
        let keys = [10, 9, 8, 7, 6, 5, 4, 3, 2, 1];
        let mut inserted = Vec::new();

        let mut tree = Tree::new();
        assert!(tree.find(&10).is_none());

        for key in keys {
            tree.insert(key, key * 2);
            inserted.push(key);
            for inserted in &inserted {
                assert_eq!(tree.find(inserted), Some(&(inserted * 2)));
            }
        }
    }

    #[test]
    fn always_adding_right() {
        let keys = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let mut inserted = Vec::new();

        let mut tree = Tree::new();
        assert!(tree.find(&1).is_none());

        for key in keys {
            tree.insert(key, key * 2);
            inserted.push(key);
            for inserted in &inserted {
                assert_eq!(tree.find(inserted), Some(&(inserted * 2)));
            }
        }
    }

    #[test]
    fn quickcheck_insert_invalid_height() {
        let mut tree = Tree::new();
        tree.insert(2, 2);
        tree.insert(0, 0);
        tree.insert(1, 1);
    }

    #[test]
    fn test_left_right_rebalance() {
        let mut tree = Tree::new();

        tree.insert(0, 0);
        tree.insert(-2, -2);
        tree.insert(-1, -1);

        assert_heights!(tree, 2, 1, 1);
    }

    #[test]
    fn test_right_left_rebalance() {
        let mut tree = Tree::new();

        tree.insert(0, 0);
        tree.insert(2, 2);
        tree.insert(1, 1);

        assert_heights!(tree, 2, 1, 1);
    }

    #[test]
    fn delete_with_no_children() {
        let mut tree = Tree::new();

        tree.insert(5, 5.to_string());

        tree.insert(3, 3.to_string());
        tree.insert(7, 7.to_string());

        assert_eq!(tree.delete(&7), Some(7.to_string()));
        assert_eq!(tree.find(&7), None);

        assert_eq!(tree.find(&3), Some(&3.to_string()));
        assert_eq!(tree.find(&5), Some(&5.to_string()));
    }

    #[test]
    fn delete_with_null_left() {
        let mut tree = Tree::new();

        tree.insert(5, 5.to_string());

        tree.insert(3, 3.to_string());
        tree.insert(7, 7.to_string());

        tree.insert(9, 9.to_string());

        assert_eq!(tree.delete(&7), Some(7.to_string()));
        assert_eq!(tree.find(&7), None);

        assert_eq!(tree.find(&3), Some(&3.to_string()));
        assert_eq!(tree.find(&5), Some(&5.to_string()));
        assert_eq!(tree.find(&9), Some(&9.to_string()));
    }

    #[test]
    fn delete_with_null_right() {
        let mut tree = Tree::new();

        tree.insert(5, 5.to_string());

        tree.insert(3, 3.to_string());
        tree.insert(7, 7.to_string());

        tree.insert(6, 6.to_string());

        assert_eq!(tree.delete(&7), Some(7.to_string()));
        assert_eq!(tree.find(&7), None);

        assert_eq!(tree.find(&3), Some(&3.to_string()));
        assert_eq!(tree.find(&5), Some(&5.to_string()));
        assert_eq!(tree.find(&6), Some(&6.to_string()));
    }

    #[test]
    fn delete_with_left_predecessor() {
        let mut tree = Tree::new();

        tree.insert(5, 5.to_string());

        tree.insert(3, 3.to_string());
        tree.insert(7, 7.to_string());

        tree.insert(6, 6.to_string());
        tree.insert(8, 8.to_string());

        assert_eq!(tree.delete(&7), Some(7.to_string()));
        assert_eq!(tree.find(&7), None);

        assert_eq!(tree.find(&3), Some(&3.to_string()));
        assert_eq!(tree.find(&5), Some(&5.to_string()));
        assert_eq!(tree.find(&6), Some(&6.to_string()));
        assert_eq!(tree.find(&8), Some(&8.to_string()));
    }

    #[test]
    fn delete_with_deeper_predecessor() {
        let mut tree = Tree::new();

        tree.insert(5, 5.to_string());

        tree.insert(3, 3.to_string());
        tree.insert(8, 8.to_string());

        tree.insert(2, 2.to_string());

        tree.insert(6, 6.to_string());
        tree.insert(9, 9.to_string());

        tree.insert(7, 7.to_string());

        assert_eq!(tree.delete(&8), Some(8.to_string()));
        assert_eq!(tree.find(&8), None);

        assert_eq!(tree.find(&2), Some(&2.to_string()));
        assert_eq!(tree.find(&3), Some(&3.to_string()));
        assert_eq!(tree.find(&5), Some(&5.to_string()));
        assert_eq!(tree.find(&7), Some(&7.to_string()));
        assert_eq!(tree.find(&9), Some(&9.to_string()));
    }

    #[test]
    fn delete_root() {
        let mut tree = Tree::new();

        tree.insert(5, 5.to_string());

        assert_eq!(tree.delete(&5), Some(5.to_string()));
        assert_eq!(tree.find(&5), None);
    }

    #[test]
    fn rotate_right_fixes_parent_pointers() {
        let mut tree = Tree::new();

        tree.insert(5, 5);
        tree.insert(3, 3);
        tree.insert(9, 9);
        tree.insert(4, 4);
        tree.insert(2, 2);
        tree.insert(1, 1);

        let three_node = tree.root().unwrap();
        let five_node = three_node.right.unwrap();
        let nine_node = unsafe { five_node.as_ref().right.unwrap() };

        let nine_node_parent = unsafe { nine_node.as_ref().parent.unwrap() };

        assert_eq!(five_node, nine_node_parent);
    }

    #[test]
    fn rotate_left_fixes_parent_pointers() {
        let mut tree = Tree::new();

        tree.insert(-5, -5);
        tree.insert(-3, -3);
        tree.insert(-9, -9);
        tree.insert(-4, -4);
        tree.insert(-2, -2);
        tree.insert(-1, -1);

        let three_node = tree.root().unwrap();
        let five_node = three_node.left.unwrap();
        let nine_node = unsafe { five_node.as_ref().left.unwrap() };

        let nine_node_parent = unsafe { nine_node.as_ref().parent.unwrap() };

        assert_eq!(five_node, nine_node_parent);
    }

    #[test]
    fn quickcheck_found_invalid_height_after_deletion() {
        let mut tree = Tree::new();

        tree.insert(77, -58);
        tree.insert(-22, -58);
        tree.insert(0, -37);
        tree.insert(-127, 79);
        tree.insert(5, 127);
        tree.insert(109, -83);
        tree.insert(-58, 91);
        tree.insert(-105, -46);
        tree.insert(-65, 8);
        tree.insert(-86, -51);
        tree.insert(45, -112);
        tree.insert(-11, 3);
        tree.insert(-39, 27);
        tree.delete(&0);
        tree.delete(&-122);
    }

    #[test]
    fn quickcheck_found_invalid_height_after_deletion2() {
        let mut tree = Tree::new();
        tree.insert(-49, -110);
        tree.insert(-107, 80);
        tree.insert(127, 59);
        tree.insert(-22, 71);
        tree.insert(-77, 0);
        tree.insert(-128, 0);
        tree.insert(-119, 17);
        tree.insert(-69, -11);
        tree.insert(-122, 29);
        tree.insert(109, -80);
        tree.insert(115, 40);
        tree.insert(-118, 53);
        tree.delete(&-49);
        tree.delete(&-77);
    }
}

#[cfg(test)]
mod quicktests {
    use std::collections::HashMap;

    use super::*;
    use crate::test::quick::Op;

    /// Applies a set of operations to a tree and a hashmap.
    /// This way we can ensure that after a random smattering of inserts
    /// and deletes we have the same set of keys in the map.
    fn do_ops<K, V>(ops: &[Op<K, V>], bst: &mut Tree<K, V>, map: &mut HashMap<K, V>)
    where
        K: std::hash::Hash + Eq + Clone + Ord,
        V: std::fmt::Debug + PartialEq + Clone,
    {
        for op in ops {
            match op {
                Op::Insert(k, v) => {
                    bst.insert(k.clone(), v.clone());
                    map.insert(k.clone(), v.clone());
                }
                Op::Remove(k) => {
                    assert_eq!(bst.delete(k), map.remove(k));
                }
            }
        }
    }

    quickcheck::quickcheck! {
        fn fuzz_multiple_operations_i8(ops: Vec<Op<i8, i8>>) -> bool {
            let mut tree = Tree::new();
            let mut map = HashMap::new();

            do_ops(&ops, &mut tree, &mut map);
            map.keys().all(|key| tree.find(key) == map.get(key))
        }
    }

    quickcheck::quickcheck! {
        fn contains(xs: Vec<i8>) -> bool {
            let mut tree = Tree::new();
            for x in &xs {
                tree.insert(*x, *x);
            }

            xs.iter().all(|x| tree.find(x) == Some(x))
        }
    }
}
