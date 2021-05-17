use bst::functional::Tree;
use criterion::{black_box, criterion_group, criterion_main, Criterion};

pub fn criterion_benchmark(c: &mut Criterion) {
    let mut unbalanced = c.benchmark_group("unbalanced");
    let get_unbalanced_tree = || {
        let mut tree = Tree::new();
        for i in (1..100).rev().map(black_box) {
            tree = tree.insert(i, i);
        }
        tree
    };
    unbalanced.bench_function("empty_inserts", |b| b.iter(get_unbalanced_tree));

    let unbalanced_tree = get_unbalanced_tree();
    unbalanced.bench_function("full_insert", |b| {
        b.iter_batched(
            || unbalanced_tree.clone(),
            |tree| tree.insert(black_box(0), black_box(0)),
            criterion::BatchSize::SmallInput,
        )
    });
    unbalanced.bench_function("full_find_found", |b| {
        b.iter_batched(
            || unbalanced_tree.clone(),
            |tree| {
                let _value = tree.find(&black_box(2));
            },
            criterion::BatchSize::SmallInput,
        )
    });
    unbalanced.bench_function("full_find_not_found", |b| {
        b.iter_batched(
            || unbalanced_tree.clone(),
            |tree| {
                let _value = tree.find(&black_box(-1));
            },
            criterion::BatchSize::SmallInput,
        )
    });
    unbalanced.bench_function("full_delete_found", |b| {
        b.iter_batched(
            || unbalanced_tree.clone(),
            |tree| tree.delete(&black_box(2)),
            criterion::BatchSize::SmallInput,
        )
    });
    unbalanced.bench_function("full_delete_not_found", |b| {
        b.iter_batched(
            || unbalanced_tree.clone(),
            |tree| tree.delete(&black_box(-1)),
            criterion::BatchSize::SmallInput,
        )
    });

    unbalanced.finish();

    let mut balanced = c.benchmark_group("balanced");
    fn fill_balanced_tree<T: std::cmp::Ord + Clone>(mut tree: Tree<T, T>, xs: &[T]) -> Tree<T, T> {
        if xs.len() < 3 {
            for x in xs {
                tree = tree.insert(x.clone(), x.clone());
            }
        } else {
            tree = tree.insert(xs[xs.len() / 2].clone(), xs[xs.len() / 2].clone());
            tree = fill_balanced_tree(tree, &xs[..xs.len() / 2]);
            tree = fill_balanced_tree(tree, &xs[xs.len() / 2 + 1..]);
        }
        tree
    }
    let get_balanced_tree = || {
        let tree = Tree::new();
        let xs = (1..100).map(black_box).collect::<Vec<_>>();
        fill_balanced_tree(tree, &xs)
    };
    balanced.bench_function("empty_inserts", |b| b.iter(get_balanced_tree));

    let balanced_tree = get_balanced_tree();
    balanced.bench_function("full_insert", |b| {
        b.iter_batched(
            || balanced_tree.clone(),
            |tree| tree.insert(black_box(0), black_box(0)),
            criterion::BatchSize::SmallInput,
        )
    });
    balanced.bench_function("full_find_found", |b| {
        b.iter_batched(
            || balanced_tree.clone(),
            |tree| {
                let _value = tree.find(&black_box(2));
            },
            criterion::BatchSize::SmallInput,
        )
    });
    balanced.bench_function("full_find_not_found", |b| {
        b.iter_batched(
            || balanced_tree.clone(),
            |tree| {
                let _value = tree.find(&black_box(-1));
            },
            criterion::BatchSize::SmallInput,
        )
    });
    balanced.bench_function("full_delete_found", |b| {
        b.iter_batched(
            || balanced_tree.clone(),
            |tree| tree.delete(&black_box(2)),
            criterion::BatchSize::SmallInput,
        )
    });
    balanced.bench_function("full_delete_not_found", |b| {
        b.iter_batched(
            || balanced_tree.clone(),
            |tree| tree.delete(&black_box(-1)),
            criterion::BatchSize::SmallInput,
        )
    });

    balanced.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
