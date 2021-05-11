use std::cmp;

pub struct Leaf;

pub struct Node<K, V> {
    key: K,
    value: V,
    left: Box<Tree<K, V>>,
    right: Box<Tree<K, V>>,
}

pub enum Tree<K, V> {
    Leaf,
    Node(Node<K, V>),
}

impl<K, V> Default for Tree<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Tree<K, V> {
    pub fn new() -> Self {
        Tree::Leaf
    }

    pub fn insert(self, k: K, v: V) -> Self
    where
        K: cmp::Ord,
    {
        match self {
            Tree::Leaf => Tree::Node(Node {
                key: k,
                value: v,
                left: Box::new(Tree::Leaf),
                right: Box::new(Tree::Leaf),
            }),
            Tree::Node(n) => match k.cmp(&n.key) {
                cmp::Ordering::Less => Tree::Node(Node {
                    left: Box::new(n.left.insert(k, v)),
                    ..n
                }),
                cmp::Ordering::Equal => Tree::Node(Node { value: v, ..n }),
                cmp::Ordering::Greater => Tree::Node(Node {
                    right: Box::new(n.right.insert(k, v)),
                    ..n
                }),
            },
        }
    }

    pub fn find(&self, k: K) -> Option<&V>
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

    pub fn delete(self, k: K) -> Self
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
                cmp::Ordering::Equal => match (n.left.as_ref(), n.right.as_ref()) {
                    (Tree::Leaf, _) => *n.right,
                    (_, Tree::Leaf) => *n.left,
                    _ => unimplemented!(),
                },
                cmp::Ordering::Greater => Tree::Node(Node {
                    right: Box::new(n.right.delete(k)),
                    ..n
                }),
            },
        }
    }

    #[allow(dead_code)]
    fn greatest_in(self) -> Self
    where
        K: cmp::Ord,
    {
        match self {
            Tree::Leaf => self,
            Tree::Node(n) => match *n.right {
                Tree::Leaf => *n.right,
                Tree::Node(r) => r.right.greatest_in(),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert() {
        let mut tree = Tree::new();
        tree = tree.insert(1, 2);

        assert_eq!(tree.find(1), Some(&2));
    }

    #[test]
    fn test_delete_no_children() {
        let mut tree = Tree::new();
        tree = tree.insert(1, 2);
        tree = tree.insert(2, 3);
        tree = tree.delete(2);

        assert_eq!(tree.find(1), Some(&2));
        assert_eq!(tree.find(2), None);
    }

    #[test]
    fn test_delete_no_left_child() {
        let mut tree = Tree::new();
        tree = tree.insert(1, 2);
        tree = tree.insert(2, 3);
        tree = tree.delete(1);

        assert_eq!(tree.find(1), None);
        assert_eq!(tree.find(2), Some(&3));
    }

    #[test]
    fn test_delete_no_right_child() {
        let mut tree = Tree::new();
        tree = tree.insert(2, 3);
        tree = tree.insert(1, 2);
        tree = tree.delete(2);

        assert_eq!(tree.find(1), Some(&2));
        assert_eq!(tree.find(2), None);
    }

    #[test]
    fn test_delete_two_children() {
        let mut tree = Tree::new();
        tree = tree.insert(2, 3);
        tree = tree.insert(1, 2);
        tree = tree.insert(3, 4);
        tree = tree.delete(2);

        assert_eq!(tree.find(1), Some(&2));
        assert_eq!(tree.find(2), None);
        assert_eq!(tree.find(3), Some(&4));
    }

    // TODO Test BST invariant
}
