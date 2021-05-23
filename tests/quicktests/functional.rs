use bst::functional::Tree;

use std::collections::{HashMap, HashSet};

use crate::Op;

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

#[quickcheck]
fn fuzz_multiple_operations_i8(ops: Vec<Op<i8, i8>>) -> bool {
    let mut tree = Tree::new();
    let mut map = HashMap::new();

    tree = do_ops(&ops, tree, &mut map);
    map.keys().all(|key| tree.find(key) == map.get(key))
}

#[quickcheck]
fn contains(xs: Vec<i8>) -> bool {
    let mut tree = Tree::new();
    for x in &xs {
        tree = tree.insert(*x, *x);
    }

    xs.iter().all(|x| tree.find(x) == Some(x))
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
