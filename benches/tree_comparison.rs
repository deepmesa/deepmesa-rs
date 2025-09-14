use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use deepmesa_collections::RedBlackTree;
use std::collections::BTreeSet;

const OPERATIONS: usize = 10_000;

fn generate_random_values(count: usize, seed: u64) -> Vec<usize> {
    let mut values = Vec::with_capacity(count);
    let mut current_seed = seed;
    for _ in 0..count {
        current_seed = current_seed.wrapping_mul(1103515245).wrapping_add(12345);
        values.push((current_seed % (count as u64 * 10)) as usize);
    }
    values
}

fn bench_insert_sequential(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_sequential");

    group.bench_function("RedBlackTree", |b| {
        b.iter_batched(
            || RedBlackTree::with_capacity(OPERATIONS),
            |mut tree| {
                for i in 0..OPERATIONS {
                    tree.insert(black_box(i));
                }
                tree
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("BTreeSet", |b| {
        b.iter_batched(
            || BTreeSet::new(), // BTreeSet doesn't have with_capacity
            |mut set| {
                for i in 0..OPERATIONS {
                    set.insert(black_box(i));
                }
                set
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_insert_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_random");
    let values = generate_random_values(OPERATIONS, 12345);

    group.bench_function("RedBlackTree", |b| {
        b.iter_batched(
            || RedBlackTree::with_capacity(OPERATIONS),
            |mut tree| {
                for &val in &values {
                    tree.insert(black_box(val));
                }
                tree
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("BTreeSet", |b| {
        b.iter_batched(
            || BTreeSet::new(),
            |mut set| {
                for &val in &values {
                    set.insert(black_box(val));
                }
                set
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_insert_reverse(c: &mut Criterion) {
    let mut group = c.benchmark_group("insert_reverse");

    group.bench_function("RedBlackTree", |b| {
        b.iter_batched(
            || RedBlackTree::with_capacity(OPERATIONS),
            |mut tree| {
                for i in (0..OPERATIONS).rev() {
                    tree.insert(black_box(i));
                }
                tree
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("BTreeSet", |b| {
        b.iter_batched(
            || BTreeSet::new(),
            |mut set| {
                for i in (0..OPERATIONS).rev() {
                    set.insert(black_box(i));
                }
                set
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_lookup_sequential(c: &mut Criterion) {
    let mut group = c.benchmark_group("lookup_sequential");

    // Pre-populate trees outside the benchmark
    let mut rb_tree = RedBlackTree::with_capacity(OPERATIONS);
    let mut bt_set = BTreeSet::new();
    for i in 0..OPERATIONS {
        rb_tree.insert(i);
        bt_set.insert(i);
    }

    group.bench_function("RedBlackTree", |b| {
        b.iter(|| {
            for i in 0..OPERATIONS {
                black_box(rb_tree.get(black_box(i)));
            }
        })
    });

    group.bench_function("BTreeSet", |b| {
        b.iter(|| {
            for i in 0..OPERATIONS {
                black_box(bt_set.contains(&black_box(i)));
            }
        })
    });

    group.finish();
}

fn bench_lookup_random(c: &mut Criterion) {
    let mut group = c.benchmark_group("lookup_random");
    let lookup_values = generate_random_values(OPERATIONS, 54321);

    // Pre-populate trees outside the benchmark
    let mut rb_tree = RedBlackTree::with_capacity(OPERATIONS);
    let mut bt_set = BTreeSet::new();
    for i in 0..OPERATIONS {
        rb_tree.insert(i);
        bt_set.insert(i);
    }

    group.bench_function("RedBlackTree", |b| {
        b.iter(|| {
            for &val in &lookup_values {
                black_box(rb_tree.get(black_box(val)));
            }
        })
    });

    group.bench_function("BTreeSet", |b| {
        b.iter(|| {
            for &val in &lookup_values {
                black_box(bt_set.contains(&black_box(val)));
            }
        })
    });

    group.finish();
}

fn bench_mixed_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("mixed_operations");

    group.bench_function("RedBlackTree", |b| {
        b.iter_batched(
            || RedBlackTree::with_capacity(OPERATIONS),
            |mut tree| {
                for i in 0..OPERATIONS / 4 {
                    // Insert two values
                    tree.insert(black_box(i));
                    tree.insert(black_box(i + OPERATIONS));

                    // Look up existing values
                    black_box(tree.get(black_box(i / 2)));
                    black_box(tree.get(black_box(i)));
                }
                tree
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("BTreeSet", |b| {
        b.iter_batched(
            || BTreeSet::new(),
            |mut set| {
                for i in 0..OPERATIONS / 4 {
                    // Insert two values
                    set.insert(black_box(i));
                    set.insert(black_box(i + OPERATIONS));

                    // Look up existing values
                    black_box(set.contains(&black_box(i / 2)));
                    black_box(set.contains(&black_box(i)));
                }
                set
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_clear(c: &mut Criterion) {
    let mut group = c.benchmark_group("clear");

    group.bench_function("RedBlackTree", |b| {
        b.iter_batched(
            || {
                let mut tree = RedBlackTree::with_capacity(OPERATIONS);
                for i in 0..OPERATIONS {
                    tree.insert(i);
                }
                tree
            },
            |mut tree| {
                tree.clear();
                tree
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("BTreeSet", |b| {
        b.iter_batched(
            || {
                let mut set = BTreeSet::new();
                for i in 0..OPERATIONS {
                    set.insert(i);
                }
                set
            },
            |mut set| {
                set.clear();
                set
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_duplicate_inserts(c: &mut Criterion) {
    let mut group = c.benchmark_group("duplicate_inserts");
    let insert_count = OPERATIONS / 10;

    group.bench_function("RedBlackTree", |b| {
        b.iter_batched(
            || {
                let mut tree = RedBlackTree::with_capacity(insert_count);
                for i in 0..insert_count {
                    tree.insert(i);
                }
                tree
            },
            |mut tree| {
                for i in 0..insert_count {
                    tree.insert(black_box(i)); // These should be ignored
                }
                tree
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("BTreeSet", |b| {
        b.iter_batched(
            || {
                let mut set = BTreeSet::new();
                for i in 0..insert_count {
                    set.insert(i);
                }
                set
            },
            |mut set| {
                for i in 0..insert_count {
                    set.insert(black_box(i)); // These should be ignored
                }
                set
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_size_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("size_scaling");

    for size in [1_000, 5_000, 10_000, 25_000].iter() {
        group.bench_with_input(BenchmarkId::new("RedBlackTree_insert", size), size, |b, &size| {
            b.iter_batched(
                || RedBlackTree::with_capacity(size),
                |mut tree| {
                    for i in 0..size {
                        tree.insert(black_box(i));
                    }
                    tree
                },
                criterion::BatchSize::SmallInput,
            )
        });

        group.bench_with_input(BenchmarkId::new("BTreeSet_insert", size), size, |b, &size| {
            b.iter_batched(
                || BTreeSet::new(),
                |mut set| {
                    for i in 0..size {
                        set.insert(black_box(i));
                    }
                    set
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }

    group.finish();
}

criterion_group!(
    tree_benches,
    bench_insert_sequential,
    bench_insert_random,
    bench_insert_reverse,
    bench_lookup_sequential,
    bench_lookup_random,
    bench_mixed_operations,
    bench_clear,
    bench_duplicate_inserts,
    bench_size_comparison
);

criterion_main!(tree_benches);