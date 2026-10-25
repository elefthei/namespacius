# namespacius

Intern paths such as `/usr/lib/x` or `std::vector`, then compare IDs instead of
strings. `namespacius` uses [bumpus](https://github.com/elefthei/bumpus) arenas,
is verified with Verus, and supports `no_std` + `alloc`.

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

**Call `free()` when you're done.** There is no `Drop` implementation; dropping
a cache without freeing it leaks both arena chunks, just as with bumpus.

## Paths and IDs

`PathId` is a `u64` newtype with equality and hashing. IDs belong to one cache;
don't compare them across caches. `PathCache::lemma_id_eq_bytes` proves, within
one cache:

```text
id_a == id_b  <==>  bytes_a == bytes_b
```

Splitting keeps empty components and matches delimiters left to right, without
overlap:

| Path | Delimiter | Components |
| --- | --- | --- |
| `""` | `/` | `[""]` |
| `/a` | `/` | `["", "a"]` |
| `a/` | `/` | `["a", ""]` |
| `a//b` | `/` | `["a", "", "b"]` |
| `a:::b` | `::` | `["a", ":b"]` |

Paths aren't normalized: `/a` differs from `a`, and `::std` differs from `std`.
`/home/foo/bar` creates four nodes because its leading empty component counts.

`len()` counts all trie nodes except the root, including prefixes you haven't
explicitly interned. IDs are dense, with numeric values `1..=len()`. Zero is the
empty root sentinel and is never returned.

`component(id)` returns the final component as `&[u8]`. `parent(id)` returns
`None` for a one-component path. Both panic on invalid IDs.

## Capacity and allocation

`new(delimiter)` allows 1,048,576 nodes, 16,777,216 component bytes, and 4,096 memo
entries. Use `with_capacity(delimiter, max_nodes, max_bytes, memo_entries)` to
choose your own. Node capacity includes the root; zero memo entries becomes one.

Empty delimiters and zero, invalid, or overflowing arena capacities return
`AllocErr::Capacity`. Failed construction frees any arenas already created.

Arena exhaustion returns `AllocErr::Exhausted`. A failed intern keeps any prefix
nodes it created; existing IDs stay valid. If a parent allocation fails after
storing its component, existing paths still work, but new edges return
`Exhausted`. The unused component stays in the arena and is never indexed.

Heap allocations for the hash table, memo, delimiter, and scratch buffers can
abort on global OOM.

## Lookup and batches

Two bumpus arenas store parent indices and component bytes. A
`hashbrown::HashTable` indexes `(parent, component)` edges and compares bytes,
so hash collisions can't merge paths. Lookup is expected O(1) per component plus
hashing and comparison. Scanning costs O(n) for a fixed delimiter, or O(n*m)
worst case for n path bytes and m delimiter bytes.

`intern` keeps an `lru` memo of full paths. Hits skip the trie walk and allocate
nothing, but still hash and compare O(n) bytes. Misses allocate a boxed key.
Fixed-seed edge hashing is deterministic; it isn't hardened against hash flooding.

`intern_batch(&[&str])` resumes at the deepest component boundary shared with
the previous path. Grouped paths avoid repeated prefix lookups; any order works.
Batch calls don't read or fill the LRU.

## Verification

The model maps each node ID to its component sequence. `intern` and
`intern_batch` return the node matching `split(path bytes, delimiter)`.
Proofs cover trie insertion, scanning, batch resumption, memo correctness,
and ID equality. They rely on these trusted operations:

- `key`: `foldhash::fast::FixedState` with a constant seed is a pure function of
  parent index and component bytes. Hashes needn't be unique.
- `EdgeTable::{new, find, insert}`: `hashbrown::HashTable` starts empty, finds
  exactly the stored matching entries under the supplied hash, and inserts the
  given pair. Rehashing uses stored hashes; lookup compares parent and arena bytes
  through bounds-checked access that handles out-of-range indices.
- `Memo::{new, get, put}`: `lru::LruCache` behaves as a map. Promotion leaves map
  contents unchanged; insertion stores the requested value and may only evict
  other keys. The verified invariant proves each stored ID matches its key.
- Bumpus's `try_allocate`, `slice_ref`, and `Layout` bridges, plus vstd axioms and
  standard-library specifications.

Use Verus `0.2026.10.04.426d8b0` and Rust `1.98.1`. Keep
`vstd =0.0.0-2026-09-06-0133` pinned to match bumpus; a second vstd version breaks
the dependency graph. Don't pass `--check-toolchain`: it rejects the older vstd
pin, while ordinary verification checks the proofs.

```sh
cargo verus verify
cargo test --release
cargo test --release --test paths multibyte_delimiter -- --nocapture
cargo test --release --test paths batch_resume_correct_on_divergence -- --nocapture
cargo bench --bench intern
cargo build --release --all-targets
```

The randomized integration test checks 5,000 generated paths against forward
and reverse `HashMap` oracles.

## Benchmarks

Corpus: 20,000 tree-ordered paths
`/usr/src/proj{0..20}/mod{0..25}/file{0..40}.rs`. Hot cases use the first 2,000.

One release-mode run on an Intel Xeon Platinum 8370C @ 2.80 GHz, x86-64 WSL2,
using Criterion 0.8.2 with 100 samples. These are Criterion's saved median point
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
hasher. The table compares complete implementations; the numbers aren't
performance targets.
