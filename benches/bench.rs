use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};

use bst::{bangsafe, immutable};

#[derive(Clone)]
enum TreeEnum<K, V> {
    Bangsafe(bangsafe::Tree<K, V>),
    Immutable(immutable::Tree<K, V>),
}

impl<K, V> TreeEnum<K, V> {
    fn find(&self, k: &K) -> Option<&V>
    where
        K: Ord,
    {
        match self {
            Self::Bangsafe(t) => t.find(k),
            Self::Immutable(t) => t.find(k),
        }
    }

    fn insert(&mut self, k: K, v: V)
    where
        K: Ord,
    {
        match self {
            Self::Bangsafe(t) => t.insert(k, v),
            Self::Immutable(t) => {
                t.insert(k, v);
            }
        }
    }

    fn delete(&mut self, k: &K)
    where
        K: Ord,
    {
        match self {
            Self::Bangsafe(t) => {
                t.delete(k);
            }
            Self::Immutable(t) => {
                t.delete(k);
            }
        }
    }
}

/// Helper to bench a function on a BST.
/// It creates a group for the given name and closure and runs tests for various sizes and
/// implementations of BSTs before finishing the group.
fn bench_helper(c: &mut Criterion, name: &str, f: impl Fn(&mut TreeEnum<i32, i32>, i32)) {
    let mut group = c.benchmark_group(name);

    for num_levels in [3, 7, 11, 15] {
        let num_nodes = 2usize.pow(num_levels as u32) - 1;
        // TODO consider `max` method on BST.
        let largest_element_in_tree = 2usize.pow(num_levels as u32) - 2;

        let immutable_tree = (0..num_nodes).fold(immutable::Tree::new(), |tree, x| {
            tree.insert(x as i32, x as i32)
        });
        let bangsafe_tree = {
            let mut tree = bangsafe::Tree::new();
            for x in 0..num_nodes {
                tree.insert(x as i32, x as i32);
            }

            tree
        };
        let tree_tests = [
            ("immutable", TreeEnum::Immutable(immutable_tree)),
            ("bangsafe", TreeEnum::Bangsafe(bangsafe_tree)),
        ];
        for (name, tree) in tree_tests {
            let id = BenchmarkId::new(name, largest_element_in_tree);

            group.bench_function(id, |b| {
                b.iter_custom(|iters| {
                    let mut time = std::time::Duration::ZERO;
                    for _ in 0..iters {
                        let mut tree = black_box(tree.clone());
                        let instant = std::time::Instant::now();
                        f(&mut tree, black_box(largest_element_in_tree as i32));
                        let elapsed = instant.elapsed();
                        time += elapsed;
                    }
                    time
                })
            });
        }
    }

    group.finish();
}

pub fn criterion_benchmark(c: &mut Criterion) {
    bench_helper(c, "find", |tree, i| {
        let _value = black_box(tree.find(&i));
    });
    bench_helper(c, "delete", |tree, i| {
        tree.delete(&i);
    });

    bench_helper(c, "insert", |tree, i| {
        tree.insert(i + 1, i + 1);
    });

    bench_helper(c, "find-miss", |tree, i| {
        let _value = black_box(tree.find(&(i + 1)));
    });
    bench_helper(c, "delete-miss", |tree, i| {
        tree.delete(&(i + 1));
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
