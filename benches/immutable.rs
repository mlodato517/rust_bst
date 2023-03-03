use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

use bst::immutable::Tree;

/// Returns how many nodes are needed to fill a binary tree with `num_levels` levels.
fn num_nodes_in_full_tree(num_levels: usize) -> usize {
    2usize.pow(num_levels as u32) - 1
}

/// Builds a tree by inserting values in an unbalanced manner. This adds elements in an
/// ascending manner to ensure the tree is unbalanced (unless it is self-balancing!).
fn get_unbalanced_tree(num_levels: usize) -> Tree<i32, i32> {
    let mut tree = Tree::new();
    let tree_size = num_nodes_in_full_tree(num_levels);
    for x in (0..).take(tree_size) {
        tree = tree.insert(x, x);
    }

    tree
}

/// Builds a tree by inserting values in a balanced manner. This adds elements so that, without
/// any self-balancing, the resultant tree will still be balanced.
///
/// It ensures there are `num_levels` of nodes, all full.
fn get_balanced_tree(num_levels: usize) -> Tree<i32, i32> {
    let tree = Tree::new();
    let tree_size = num_nodes_in_full_tree(num_levels);
    let xs = (0..).take(tree_size).collect::<Vec<_>>();
    fill_balanced_tree(tree, &xs)
}

/// Recursive helper for [`get_balanced_tree`].
fn fill_balanced_tree(mut tree: Tree<i32, i32>, xs: &[i32]) -> Tree<i32, i32> {
    if !xs.is_empty() {
        let mid = xs.len() / 2;
        tree = tree.insert(xs[mid], xs[mid]);
        tree = fill_balanced_tree(tree, &xs[..mid]);
        tree = fill_balanced_tree(tree, &xs[mid + 1..]);
    }
    tree
}

/// Helper to bench a function on a BST.
/// It creates a group for the given name and closure and runs tests for various sizes and
/// shapes of BSTs before finishing the group.
fn bench_helper(c: &mut Criterion, name: &str, f: impl Fn(&Tree<i32, i32>, i32)) {
    let mut group = c.benchmark_group(name);

    // For trees of size 2^3, 2^7, etc....
    for num_levels in [3, 7, 11, 15] {
        // Test unbalanced and balanced trees.
        let tree_tests = [
            ("unbalanced", get_unbalanced_tree(num_levels)),
            ("balanced", get_balanced_tree(num_levels)),
        ];
        // TODO consider `max` method on BST.
        let largest_element_in_tree = 2usize.pow(num_levels as u32) - 2;
        for (name, tree) in tree_tests {
            let id = BenchmarkId::new(name.to_string(), largest_element_in_tree);

            group.bench_with_input(id, &largest_element_in_tree, |b, _| {
                b.iter(|| {
                    f(&tree, largest_element_in_tree as i32);
                })
            });
        }
    }

    group.finish();
}

/// Test BSTs. All tests are run against balanced and unbalanced trees of various sizes and test
/// successful and unsuccessful actions.
pub fn criterion_benchmark(c: &mut Criterion) {
    bench_helper(c, "find", |tree, i| {
        let _value = tree.find(&i);
    });
    bench_helper(c, "delete", |tree, i| {
        let _new_tree = tree.delete(&i);
    });

    bench_helper(c, "insert", |tree, i| {
        let _new_tree = tree.insert(i + 1, i + 1);
    });

    bench_helper(c, "find-miss", |tree, i| {
        let _value = tree.find(&(i + 1));
    });
    bench_helper(c, "delete-miss", |tree, i| {
        let _new_tree = tree.delete(&(i + 1));
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
