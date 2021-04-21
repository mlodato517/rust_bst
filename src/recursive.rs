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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert() {
        let tree = Tree::new();
        let tree = tree.insert(1, 2);

        assert_eq!(tree.find(1), Some(&2));
    }

    // TODO Test BST invariant
}
