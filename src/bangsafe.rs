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
    // This is a `Link` instead of an `Option<Node>` so that it can be moved around with the `Tree`
    // without the children's parent pointers breaking.
    root: Link<K, V>,
}

impl<K, V> Default for Tree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Drop for Tree<K, V> {
    // TODO stack based drop
    fn drop(&mut self) {
        if let Some(mut root) = self.root.take().0 {
            // SAFETY: We own the root we're dropping so this won't be called twice. The root was
            // initially allocated using `Box::new` (in `Node::new_boxed`) so this should be well
            // aligned, etc.
            unsafe { drop(Box::from_raw(root.as_mut())) };
        }
    }
}

impl<K, V> Clone for Tree<K, V>
where
    K: Clone,
    V: Clone,
{
    // TODO stack based Clone
    fn clone(&self) -> Self {
        let root = self.root().map(|root| {
            let new_root = Box::leak(Box::new(root.clone()));
            new_root.fix_left_child_parent();
            new_root.fix_right_child_parent();
            NonNull::from(new_root)
        });
        Self { root: Link(root) }
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
        Self { root: Link(None) }
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
            Some(root) => {
                root.insert(key, value);
                self.root.balance();
            }
            None => self.root = Link(Some(NonNull::from(Box::leak(Node::new_boxed(key, value))))),
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
        match self.root_mut().map(|root| root.delete(key)) {
            Some(DeleteResult::DeleteSelf) => {
                let deleted = self.root.take().0.expect("Deleting root implies root");
                // SAFETY: Getting `DeleteSelf` here means we deleted the root and it had no
                // children. This means nothing references it except this `Tree`. We just called
                // `self.root.take()` so now the `Tree` doesn't reference it either. So nothing
                // could dereference the value after this.
                unsafe { Some(Node::take_value(deleted)) }
            }
            Some(DeleteResult::DeletedChild(value)) => {
                self.root.balance();
                Some(value)
            }
            None | Some(DeleteResult::NotFound) => None,
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
        unsafe { self.root.0.as_ref().map(|root| root.as_ref()) }
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
        unsafe { self.root.0.as_mut().map(|root| root.as_mut()) }
    }
}

struct Link<K, V>(Option<NonNull<Node<K, V>>>);

impl<K, V> Clone for Link<K, V> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
impl<K, V> Copy for Link<K, V> {}

impl<K, V> Link<K, V> {
    fn root(&self) -> Option<&Node<K, V>> {
        // SAFETY: If the node is not `None` then it is a valid `Node`. Because we take `&self`
        // here, there can be no aliasing with `self.root_mut()`. There can only be aliasing with
        // `self.0.unwrap().as_mut()`. This code would be unsafe so it'd be the caller's
        // responsibility to ensure there is no existing borrow of the inner pointer.
        //
        // This isn't the sexiest guarantee but it feels similar to `ManuallyDrop::drop`. It's
        // unsafe to drop it because _later_ it could be dereferenced (or there is a current
        // reference).
        unsafe { self.0.as_ref().map(|ptr| ptr.as_ref()) }
    }

    fn root_mut(&mut self) -> Option<&mut Node<K, V>> {
        unsafe { self.0.as_mut().map(|ptr| ptr.as_mut()) }
    }

    fn take(&mut self) -> Self {
        Link(self.0.take())
    }

    // /// # Safety
    // ///
    // /// The caller must ensure that the value of the passed node is never referenced.
    // unsafe fn take_value(mut self) -> Option<V> {
    //     self.0.take().map(|mut ptr| {
    //         let mut node = *Box::from_raw(ptr.as_mut());
    //         node.height = VALUE_REMOVED;
    //         ManuallyDrop::take(&mut node.value)
    //     })
    // }

    fn balance(&mut self) {
        let Some(root) = self.root_mut() else {
            return;
        };
        // TODO this is probably inefficient - inlining this probably allows us to avoid checks
        // (e.g. if we just inserted into the right child, we don't need to check if the left node
        // is taller) but this currently matches the immutable tree so it's a better performance
        // comparison.
        //
        // TODO there are lots of duplicate `is_null()` and `match Option<>` branches in here.
        //
        // See https://en.wikipedia.org/wiki/AVL_tree#Rebalancing for terminology.
        root.fix_height();
        match (root.balance_factor(), root.left(), root.right()) {
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
            let Some(root) = self.root() else {
                return;
            };
            let left_height = root.left().map_or(0, |n| n.height);
            let right_height = root.right().map_or(0, |n| n.height);
            assert_eq!(root.height, left_height.max(right_height) + 1);
            assert!(left_height.abs_diff(right_height) <= 1);
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
    fn rotate_right(&mut self) {
        let mut old_root = self.take();
        let old_root = old_root.root_mut().expect("Cannot rotate empty tree/node.");
        // let old_root = unsafe { old_root.as_mut() };

        let mut new_root = old_root.left.take();
        let new_root = new_root.root_mut().expect("Rotate right => left child");

        let old_parent = old_root.parent;
        let old_right = new_root.right.take();

        // NB We can skip `fix_right_child_parent` here because we have everything we need.
        old_root.parent = Link(Some(new_root.into()));
        old_root.left = old_right;
        old_root.fix_left_child_parent();
        old_root.fix_height();

        new_root.parent = old_parent;
        new_root.right = Link(Some(old_root.into()));
        new_root.fix_height();
        self.0 = Some(new_root.into());
    }

    fn rotate_left(&mut self) {
        let mut old_root = self.take();
        let old_root = old_root
            .root_mut()
            .expect("Rotating a tree requires a root");

        let mut new_root = old_root.right.take();
        let new_root = new_root.root_mut().expect("Rotate left => right child");

        let old_left = new_root.left.take();

        // NB We can skip `fix_right_child_parent` here because we have everything we need.
        old_root.parent = Link(Some(new_root.into()));
        old_root.right = old_left;
        old_root.fix_right_child_parent();
        old_root.fix_height();

        new_root.parent = Link(None);
        new_root.left = Link(Some(old_root.into()));
        new_root.fix_height();
        self.0 = Some(new_root.into());
    }

    fn rotate_right_left(&mut self) {
        self.root_mut()
            .expect("Rotating a tree requires a root")
            .right
            .rotate_right();
        self.rotate_left();
    }
    fn rotate_left_right(&mut self) {
        self.root_mut()
            .expect("Rotating a tree requires a root")
            .left
            .rotate_left();
        self.rotate_right();
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
    left: Link<K, V>,
    right: Link<K, V>,
    height: usize,
    parent: Link<K, V>,
}

impl<K, V> Drop for Node<K, V> {
    // TODO Stack based drop
    fn drop(&mut self) {
        // SAFETY: Dropping a node doesn't drop its parent and we are the only owners of these
        // children so we won't drop them twice. They were initially allocated using `Box::new` (in
        // `Node::new_boxed`) so they should be well aligned, etc.
        unsafe {
            if let Some(mut left) = self.left.0.take() {
                drop(Box::from_raw(left.as_mut()));
            }
            if let Some(mut right) = self.right.0.take() {
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

impl<K, V> Clone for Node<K, V>
where
    K: Clone,
    V: Clone,
{
    // TODO stack based Clone
    fn clone(&self) -> Self {
        let left = self.left().map(|left| {
            let new_left = Box::leak(Box::new(left.clone()));
            new_left.fix_left_child_parent();
            new_left.fix_right_child_parent();
            NonNull::from(new_left)
        });
        let right = self.right().map(|right| {
            let new_right = Box::leak(Box::new(right.clone()));
            new_right.fix_left_child_parent();
            new_right.fix_right_child_parent();
            NonNull::from(new_right)
        });
        Self {
            height: self.height,
            key: self.key.clone(),
            value: self.value.clone(),
            left: Link(left),
            right: Link(right),
            parent: self.parent,
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
            left: Link(None),
            parent: Link(None),
            right: Link(None),
            value: ManuallyDrop::new(value),
        })
    }

    fn left(&self) -> Option<&Self> {
        self.left.root()
    }

    fn right(&self) -> Option<&Self> {
        self.right.root()
    }

    fn left_mut(&mut self) -> Option<&mut Self> {
        self.left.root_mut()
    }

    fn right_mut(&mut self) -> Option<&mut Self> {
        self.right.root_mut()
    }

    fn fix_left_child_parent(&mut self) {
        let self_ptr = NonNull::from(&*self);
        if let Some(left) = self.left_mut() {
            left.parent = Link(Some(self_ptr));
        }
    }

    fn fix_right_child_parent(&mut self) {
        let self_ptr = NonNull::from(&*self);
        if let Some(right) = self.right_mut() {
            right.parent = Link(Some(self_ptr));
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
                    self.left.balance();
                }
                None => {
                    let mut new_left = Self::new_boxed(key, value);
                    new_left.parent = Link(Some(self.into()));
                    self.left = Link(Some(NonNull::from(Box::leak(new_left))));
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
                    self.right.balance();
                }
                None => {
                    let mut new_right = Self::new_boxed(key, value);
                    new_right.parent = Link(Some(self.into()));
                    self.right = Link(Some(NonNull::from(Box::leak(new_right))));
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
        match key.cmp(&self.key) {
            Ordering::Less => match self.left_mut().map(|n| n.delete(key)) {
                Some(DeleteResult::DeleteSelf) => {
                    let deleted_left = self.left.0.take().expect("Deleting left => left");
                    // SAFETY: Getting `DeleteSelf` here means we deleted the left child and it had
                    // no children. This means nothing references it except this `Node`. We just
                    // called `self.left.take()` so now this `Node` doesn't reference it either. So
                    // nothing could dereference the value after this.
                    unsafe { DeleteResult::DeletedChild(Node::take_value(deleted_left)) }
                }
                Some(delete_result @ DeleteResult::DeletedChild(_)) => {
                    self.left.balance();
                    delete_result
                }
                None | Some(DeleteResult::NotFound) => DeleteResult::NotFound,
            },
            Ordering::Equal => match (self.left.0.take(), self.right.0.take()) {
                // We'll let our parent drop us and take our value
                (None, None) => DeleteResult::DeleteSelf,
                (None, Some(mut to_delete)) => {
                    // TODO Optimize - if we're the root (should be rare), we have to do the below.
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
                                self.right = Link(Some(right));
                                self.left = Link(Some(left_node));

                                // Remember - we deleted from largets item from the left tree!
                                self.left.balance();
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
                                self.right = Link(Some(right));
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
                    let deleted_right = self.right.0.take().expect("Deleting implies existence");
                    // SAFETY: Getting `DeleteSelf` here means we deleted the right child and it
                    // had no children. This means nothing references it except this `Node`. We
                    // just called `self.right.take()` so now this `Node` doesn't reference it
                    // either. So nothing could dereference the value after this.
                    unsafe { DeleteResult::DeletedChild(Node::take_value(deleted_right)) }
                }
                Some(delete_result @ DeleteResult::DeletedChild(_)) => {
                    self.right.balance();
                    delete_result
                }
                None | Some(DeleteResult::NotFound) => DeleteResult::NotFound,
            },
        }
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
    fn delete_largest(&mut self) -> DeleteResult<NonNull<Self>> {
        let Some(right) = self.right.0.as_mut() else {
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
                self.right = Link(right.left.0.take());
                self.fix_right_child_parent();
                DeleteResult::DeletedChild(right.into())
            }
            result @ DeleteResult::DeletedChild(_) => {
                self.right.balance();
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
        let five_node = three_node.right.0.unwrap();
        let nine_node = unsafe { five_node.as_ref().right.0.unwrap() };

        let nine_node_parent = unsafe { nine_node.as_ref().parent.0.unwrap() };

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
        let five_node = three_node.left.0.unwrap();
        let nine_node = unsafe { five_node.as_ref().left.0.unwrap() };

        let nine_node_parent = unsafe { nine_node.as_ref().parent.0.unwrap() };

        assert_eq!(five_node, nine_node_parent);
    }

    #[test]
    fn clone_works() {
        let mut tree = {
            let mut tree = Tree::new();

            tree.insert(5, 5);

            tree.insert(3, 3);
            tree.insert(7, 7);

            tree.insert(1, 1);
            tree.insert(4, 4);
            tree.insert(6, 6);
            tree.insert(8, 8);

            tree.clone()
        };

        let five_node = tree.root.0.unwrap();

        // Ensure root children are fixed
        let three_node = unsafe { five_node.as_ref().left.0.unwrap() };
        let three_node_parent = unsafe { three_node.as_ref().parent.0.unwrap() };
        assert_eq!(five_node, three_node_parent);

        let seven_node = unsafe { five_node.as_ref().right.0.unwrap() };
        let seven_node_parent = unsafe { seven_node.as_ref().parent.0.unwrap() };
        assert_eq!(five_node, seven_node_parent);

        // Ensure deeper children are fixed
        let one_node = unsafe { three_node.as_ref().left.0.unwrap() };
        let one_node_parent = unsafe { one_node.as_ref().parent.0.unwrap() };
        assert_eq!(three_node, one_node_parent);

        let four_node = unsafe { three_node.as_ref().right.0.unwrap() };
        let four_node_parent = unsafe { four_node.as_ref().parent.0.unwrap() };
        assert_eq!(three_node, four_node_parent);

        let six_node = unsafe { five_node.as_ref().left.0.unwrap() };
        let six_node_parent = unsafe { six_node.as_ref().parent.0.unwrap() };
        assert_eq!(five_node, six_node_parent);

        let eight_node = unsafe { five_node.as_ref().right.0.unwrap() };
        let eight_node_parent = unsafe { eight_node.as_ref().parent.0.unwrap() };
        assert_eq!(five_node, eight_node_parent);

        assert_eq!(tree.delete(&1), Some(1));
        assert_eq!(tree.delete(&3), Some(3));
        assert_eq!(tree.delete(&4), Some(4));

        assert_eq!(tree.delete(&7), Some(7));
        assert_eq!(tree.delete(&6), Some(6));
        assert_eq!(tree.delete(&8), Some(8));
        assert_eq!(tree.delete(&5), Some(5));
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
                Op::Iter => {}
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
