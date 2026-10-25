use criterion::{BatchSize, Criterion, Throughput};
use namespacius::{PathCache, PathId};
use std::collections::HashMap;
use std::hint::black_box;

// Benchmark-only ownership guard: PathCache itself deliberately has no Drop.
struct CacheGuard(Option<PathCache>);

impl CacheGuard {
    fn new() -> Self {
        Self(Some(PathCache::new("/").expect("benchmark cache allocation")))
    }
}

impl Drop for CacheGuard {
    fn drop(&mut self) {
        if let Some(cache) = self.0.take() {
            cache.free();
        }
    }
}

fn main() {
    let mut criterion = Criterion::default().configure_from_args();
    let mut corpus = Vec::with_capacity(20_000);
    for project in 0..20 {
        for module in 0..25 {
            for file in 0..40 {
                corpus.push(format!("/usr/src/proj{project}/mod{module}/file{file}.rs"));
            }
        }
    }
    assert_eq!(corpus.len(), 20_000);
    let paths: Vec<&str> = corpus.iter().map(String::as_str).collect();
    let hot_paths = &paths[..2_000];

    let mut intern = criterion.benchmark_group("intern");
    intern.throughput(Throughput::Elements(paths.len() as u64));
    intern.bench_function("cold", |b| {
        // Setup and guard destruction (including free) are outside the timer.
        // PerIteration prevents Criterion from retaining batches of arena chunks.
        b.iter_batched_ref(
            CacheGuard::new,
            |guard| {
                let cache = guard.0.as_mut().unwrap();
                for path in &paths {
                    black_box(cache.intern(black_box(path)).expect("intern corpus"));
                }
            },
            BatchSize::PerIteration,
        );
    });
    intern.throughput(Throughput::Elements(hot_paths.len() as u64));
    intern.bench_function("hot", |b| {
        let mut guard = CacheGuard::new();
        let cache = guard.0.as_mut().unwrap();
        for path in hot_paths {
            cache.intern(path).expect("prefill memo");
        }
        b.iter(|| {
            for path in hot_paths {
                black_box(cache.intern(black_box(path)).expect("memo hit"));
            }
        });
    });
    intern.finish();

    let mut batch = criterion.benchmark_group("intern_batch");
    batch.throughput(Throughput::Elements(paths.len() as u64));
    batch.bench_function("cold", |b| {
        b.iter_batched_ref(
            CacheGuard::new,
            |guard| {
                // Return the IDs so Criterion also drops the output after timing.
                black_box(
                    guard.0.as_mut().unwrap()
                        .intern_batch(black_box(paths.as_slice()))
                        .expect("intern batch corpus"),
                )
            },
            BatchSize::PerIteration,
        );
    });
    batch.finish();

    let mut baseline = criterion.benchmark_group("baseline_hashmap");
    baseline.throughput(Throughput::Elements(paths.len() as u64));
    baseline.bench_function("cold", |b| {
        b.iter_batched_ref(
            // Match PathCache's initial edge-index capacity; neither pre-sizes
            // its lookup table to the full corpus. Both grow while timed.
            || HashMap::<String, PathId>::with_capacity(1 << 12),
            |map| {
                for path in &paths {
                    let next = PathId(map.len() as u64 + 1);
                    black_box(map.entry(black_box(*path).to_owned()).or_insert(next));
                }
            },
            BatchSize::PerIteration,
        );
    });
    baseline.throughput(Throughput::Elements(hot_paths.len() as u64));
    baseline.bench_function("hot", |b| {
        let mut map = HashMap::<String, PathId>::with_capacity(1 << 12);
        for path in hot_paths {
            let next = PathId(map.len() as u64 + 1);
            map.entry((*path).to_owned()).or_insert(next);
        }
        b.iter(|| {
            for path in hot_paths {
                black_box(map.get(black_box(*path)).expect("prefilled path"));
            }
        });
    });
    baseline.finish();
    criterion.final_summary();
}
