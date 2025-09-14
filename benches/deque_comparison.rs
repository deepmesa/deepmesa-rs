use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use deepmesa_collections::CircularDeque;
use std::collections::VecDeque;

const OPERATIONS: usize = 10_000;

fn bench_push_back(c: &mut Criterion) {
    let mut group = c.benchmark_group("push_back");

    group.bench_function("CircularDeque", |b| {
        b.iter_batched(
            || CircularDeque::with_capacity(OPERATIONS),
            |mut deque| {
                for i in 0..OPERATIONS {
                    deque.push_back(black_box(i));
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("VecDeque", |b| {
        b.iter_batched(
            || VecDeque::with_capacity(OPERATIONS),
            |mut deque| {
                for i in 0..OPERATIONS {
                    deque.push_back(black_box(i));
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_push_front(c: &mut Criterion) {
    let mut group = c.benchmark_group("push_front");

    group.bench_function("CircularDeque", |b| {
        b.iter_batched(
            || CircularDeque::with_capacity(OPERATIONS),
            |mut deque| {
                for i in 0..OPERATIONS {
                    deque.push_front(black_box(i));
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("VecDeque", |b| {
        b.iter_batched(
            || VecDeque::with_capacity(OPERATIONS),
            |mut deque| {
                for i in 0..OPERATIONS {
                    deque.push_front(black_box(i));
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_pop_back(c: &mut Criterion) {
    let mut group = c.benchmark_group("pop_back");

    group.bench_function("CircularDeque", |b| {
        b.iter_batched(
            || {
                let mut deque = CircularDeque::with_capacity(OPERATIONS);
                for i in 0..OPERATIONS {
                    deque.push_back(i);
                }
                deque
            },
            |mut deque| {
                while !deque.is_empty() {
                    black_box(deque.pop_back());
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("VecDeque", |b| {
        b.iter_batched(
            || {
                let mut deque = VecDeque::with_capacity(OPERATIONS);
                for i in 0..OPERATIONS {
                    deque.push_back(i);
                }
                deque
            },
            |mut deque| {
                while !deque.is_empty() {
                    black_box(deque.pop_back());
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_pop_front(c: &mut Criterion) {
    let mut group = c.benchmark_group("pop_front");

    group.bench_function("CircularDeque", |b| {
        b.iter_batched(
            || {
                let mut deque = CircularDeque::with_capacity(OPERATIONS);
                for i in 0..OPERATIONS {
                    deque.push_back(i);
                }
                deque
            },
            |mut deque| {
                while !deque.is_empty() {
                    black_box(deque.pop_front());
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("VecDeque", |b| {
        b.iter_batched(
            || {
                let mut deque = VecDeque::with_capacity(OPERATIONS);
                for i in 0..OPERATIONS {
                    deque.push_back(i);
                }
                deque
            },
            |mut deque| {
                while !deque.is_empty() {
                    black_box(deque.pop_front());
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_mixed_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("mixed_operations");

    group.bench_function("CircularDeque", |b| {
        b.iter_batched(
            || CircularDeque::with_capacity(OPERATIONS),
            |mut deque| {
                for i in 0..OPERATIONS / 4 {
                    deque.push_back(black_box(i));
                    deque.push_front(black_box(i + OPERATIONS));
                    if i % 2 == 0 {
                        black_box(deque.pop_back());
                    } else {
                        black_box(deque.pop_front());
                    }
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("VecDeque", |b| {
        b.iter_batched(
            || VecDeque::with_capacity(OPERATIONS),
            |mut deque| {
                for i in 0..OPERATIONS / 4 {
                    deque.push_back(black_box(i));
                    deque.push_front(black_box(i + OPERATIONS));
                    if i % 2 == 0 {
                        black_box(deque.pop_back());
                    } else {
                        black_box(deque.pop_front());
                    }
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_with_capacity(c: &mut Criterion) {
    let mut group = c.benchmark_group("with_capacity");

    group.bench_function("CircularDeque_push_back", |b| {
        b.iter_batched(
            || CircularDeque::with_capacity(OPERATIONS),
            |mut deque| {
                for i in 0..OPERATIONS {
                    deque.push_back(black_box(i));
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("VecDeque_push_back", |b| {
        b.iter_batched(
            || VecDeque::with_capacity(OPERATIONS),
            |mut deque| {
                for i in 0..OPERATIONS {
                    deque.push_back(black_box(i));
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

fn bench_random_access(c: &mut Criterion) {
    let mut group = c.benchmark_group("random_access");

    // Pre-populate deques outside the benchmark
    let mut circular_deque = CircularDeque::with_capacity(OPERATIONS);
    let mut vec_deque = VecDeque::with_capacity(OPERATIONS);
    for i in 0..OPERATIONS {
        circular_deque.push_back(i);
        vec_deque.push_back(i);
    }

    group.bench_function("CircularDeque_get", |b| {
        b.iter(|| {
            for i in 0..OPERATIONS {
                black_box(circular_deque.get(black_box(i)));
            }
        })
    });

    group.bench_function("VecDeque_get", |b| {
        b.iter(|| {
            for i in 0..OPERATIONS {
                black_box(vec_deque.get(black_box(i)));
            }
        })
    });

    group.finish();
}

fn bench_size_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("size_scaling");

    for size in [1_000, 5_000, 10_000, 25_000].iter() {
        group.bench_with_input(BenchmarkId::new("CircularDeque_push_back", size), size, |b, &size| {
            b.iter_batched(
                || CircularDeque::with_capacity(size),
                |mut deque| {
                    for i in 0..size {
                        deque.push_back(black_box(i));
                    }
                    deque
                },
                criterion::BatchSize::SmallInput,
            )
        });

        group.bench_with_input(BenchmarkId::new("VecDeque_push_back", size), size, |b, &size| {
            b.iter_batched(
                || VecDeque::with_capacity(size),
                |mut deque| {
                    for i in 0..size {
                        deque.push_back(black_box(i));
                    }
                    deque
                },
                criterion::BatchSize::SmallInput,
            )
        });
    }

    group.finish();
}

fn bench_alternating_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("alternating_operations");

    group.bench_function("CircularDeque", |b| {
        b.iter_batched(
            || CircularDeque::with_capacity(OPERATIONS),
            |mut deque| {
                // Alternating push/pop pattern that tests wrapping behavior
                for i in 0..OPERATIONS / 2 {
                    deque.push_back(black_box(i));
                    deque.push_front(black_box(i + OPERATIONS));
                    if !deque.is_empty() {
                        black_box(deque.pop_back());
                    }
                    if !deque.is_empty() {
                        black_box(deque.pop_front());
                    }
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.bench_function("VecDeque", |b| {
        b.iter_batched(
            || VecDeque::with_capacity(OPERATIONS),
            |mut deque| {
                // Same alternating push/pop pattern
                for i in 0..OPERATIONS / 2 {
                    deque.push_back(black_box(i));
                    deque.push_front(black_box(i + OPERATIONS));
                    if !deque.is_empty() {
                        black_box(deque.pop_back());
                    }
                    if !deque.is_empty() {
                        black_box(deque.pop_front());
                    }
                }
                deque
            },
            criterion::BatchSize::SmallInput,
        )
    });

    group.finish();
}

criterion_group!(
    deque_benches,
    bench_push_back,
    bench_push_front,
    bench_pop_back,
    bench_pop_front,
    bench_mixed_operations,
    bench_with_capacity,
    bench_random_access,
    bench_size_comparison,
    bench_alternating_operations
);

criterion_main!(deque_benches);