//! This crate exposes various choices for Binary Search Trees (BSTs)
//! mostly for educational purposes.
//!
//! ## Binary Search Tree
//!
//! A Binary Search Tree is a data structure supporting operations to
//! insert, find, and delete stored records. BSTs are typically defined
//! recursively using the notion of a `Node`. A `Node` will typically store
//! some sort of value (the value that was inserted, for example) and will
//! sometimes have child `Node`s. The most important invariants of a BST are:
//!
//! 1. For every `Node` in a BST, all the `Node`s in its left subtree have a
//!    value less than its own value.
//! 2. For every `Node` in a BST, all the `Node`s in its right subtree have a
//!    value greater than its own value.
//!
//! > Note that some `Node`s have no children. These `Node`s are called "leaf nodes".
//!
//! The benefits of these invariants are many. For instance, searching for
//! values in the tree takes `O(height)` (where `height` is defined as the longest
//! path from the root `Node` to a leaf `Node`). With clever construction the
//! height of a BST can be limited to `O(lg N)` where `N` is the number of nodes
//! in the tree. BSTs also naturally support sorted iteration by visiting the
//! left subtree, then the subtree root, then the right subtree.

#![deny(missing_docs, clippy::clone_on_ref_ptr)]

pub mod functional;
