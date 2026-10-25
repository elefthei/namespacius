# namespacius

Verus-verified delimiter-separated path interning on [bumpus](https://github.com/elefthei/bumpus) arenas. `no_std` + `alloc`.

```rust
use namespacius::PathCache;

let mut cache = PathCache::new("::").unwrap();
let id = cache.intern("a:::b").unwrap();
assert_eq!(cache.len(), 2);
assert_eq!(cache.component(id), b":b");
assert_eq!(cache.component(cache.parent(id).unwrap()), b"a");
assert_eq!(cache.intern("a:::b").unwrap(), id);
cache.free();
```

## Contract

`PathId` is a `u64` newtype with equality and hashing. IDs are dense and local to one cache; never compare IDs from different caches. Root node zero is an empty sentinel and is never returned. `len()` counts all trie nodes except the root, including prefix nodes that were not explicitly interned. Valid numeric IDs are `1..=len()`.

The ghost view maps each node ID to its component sequence. `intern` and `intern_batch` return the node whose components equal `split(path bytes, delimiter)`. `PathCache::lemma_id_eq_bytes` proves, for IDs returned by one cache:

```text
id_a == id_b  <==>  bytes_a == bytes_b
```

Splitting is leftmost, non-overlapping, and preserves empty components:

| Path | Delimiter | Components |
| --- | --- | --- |
| `""` | `/` | `[""]` |
| `/a` | `/` | `["", "a"]` |
| `a/` | `/` | `["a", ""]` |
| `a//b` | `/` | `["a", "", "b"]` |
| `a:::b` | `::` | `["a", ":b"]` |

No normalization occurs: `/a` differs from `a`, `::std` differs from `std`, and `/home/foo/bar` creates **four** nodes. `parent` returns `None` for a one-component path; `component` returns `&[u8]`. Invalid IDs panic at these runtime accessors.

`new(delimiter)` uses capacities of 1,048,576 nodes, 16,777,216 component bytes, and 4,096 memo entries. `with_capacity(delimiter, max_nodes, max_bytes, memo_entries)` includes the root in node capacity. Zero memo entries is rounded up to one. Empty delimiters, zero arena capacities, and invalid/overflowing arena capacities return `AllocErr::Capacity`.

Existing IDs never invalidate. Arena exhaustion returns `AllocErr::Exhausted`; exhaustion partway through a path retains valid prefix nodes. A failed parent push may leave an unindexed component tail; further new edges then return `Exhausted` rather than reusing the wrong bytes. Existing paths remain usable. Heap-side hash-table, memo, delimiter, and scratch allocations can abort on global OOM.

**Call `free()` when finished.** There is no `Drop`, matching bumpus: dropping a cache without freeing it leaks both arena chunks. Construction frees any arenas already created if a fallible arena operation fails.

## Lookup and batching

Nodes store parent indices and component bytes in two bumpus arenas. A heap-side `hashbrown::HashTable` indexes `(parent, component)` edges and compares the actual bytes, so hash collisions cannot merge paths. Lookup is expected O(1) per component plus byte hashing/comparison. Scanning costs O(n) for a fixed delimiter, or O(n*m) worst case for n path bytes and m delimiter bytes.

`intern` uses an `lru` memo keyed by full path bytes. Hits perform O(n) hashing/comparison, allocate nothing, and avoid the trie walk. Misses allocate a boxed memo key. Fixed-seed edge hashing is deterministic, not hardened against adversarial hash flooding.

`intern_batch(&[&str])` resumes each walk at the deepest component boundary shared with the preceding input. Tree-ordered paths avoid repeated prefix lookups; arbitrary order is also correct. Batch calls neither consult nor populate the LRU.

## Verification and trust

The trie, insertion, scan, batch resumption, memo correctness invariant, and ID-equality theorems are verified. Trusted leaves are:

- `key`: `foldhash::fast::FixedState` with a constant seed is a pure function of parent index and component bytes. No collision-freedom assumption.
- `EdgeTable::{new, find, insert}`: `hashbrown::HashTable` starts empty, finds exactly stored matching entries under the supplied hash, and inserts the given pair. Rehashing uses each entry's stored hash; lookup compares parent and arena bytes with total, bounds-checked arena access.
- `Memo::{new, get, put}`: `lru::LruCache` acts as a map. Promotion leaves map contents unchanged; insertion installs the requested value and may only evict other keys. The verified invariant establishes that memo values are the correct IDs for their keys.
- Bumpus's `try_allocate`, `slice_ref`, and `Layout` bridges, plus vstd axioms and standard-library specifications.

Toolchain: Verus `0.2026.10.04.426d8b0`, Rust `1.98.1`. The exact `vstd =0.0.0-2026-09-06-0133` pin matches bumpus; a second vstd version breaks the dependency graph. Do **not** pass `--check-toolchain`: it rejects the older vstd pin, while ordinary verification checks these proofs.

```sh
cargo verus verify
cargo test --release
cargo test --release --test paths multibyte_delimiter -- --nocapture
cargo test --release --test paths batch_resume_correct_on_divergence -- --nocapture
cargo bench --bench intern
cargo build --release --all-targets
```

The randomized integration test checks 5,000 generated paths against forward and reverse `HashMap` oracles. Benchmark corpus: 20,000 tree-ordered paths `/usr/src/proj{0..20}/mod{0..25}/file{0..40}.rs`; hot cases use the first 2,000 paths.

## Local benchmark

One release-mode run on an Intel Xeon Platinum 8370C @ 2.80 GHz, x86-64 WSL2,
using Criterion 0.8.2 with 100 samples. Values are Criterion's saved median point
estimates, not the console's regression estimates. Cold setup and teardown,
including arena freeing, are outside the timed section.

| Benchmark | Paths per iteration | Median per iteration | Median ns/path |
| --- | ---: | ---: | ---: |
| `intern/cold` | 20,000 | 6.382 ms | 319.11 |
| `intern/hot` | 2,000 | 46.424 µs | 23.21 |
| `intern_batch/cold` | 20,000 | 1.491 ms | 74.57 |
| `baseline_hashmap/cold` | 20,000 | 2.704 ms | 135.19 |
| `baseline_hashmap/hot` | 2,000 | 65.659 µs | 32.83 |

The baseline uses `std::collections::HashMap<String, PathId>` with its default
hasher; these measurements compare the complete implementations, not just their
data structures. There is no performance acceptance threshold.
