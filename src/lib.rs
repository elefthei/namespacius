#![cfg_attr(not(verus_only), allow(dead_code, unused_braces))]
#![no_std]
//! Verus-verified delimiter-separated path interning on bumpus arenas (`no_std` + `alloc`).
//!
//! # Contract
//! The cache view is a sequence of component sequences indexed by dense, cache-local
//! [`PathId`] values (a `u64` newtype). Node zero is the empty root sentinel and is
//! never returned. Successful [`PathCache::intern`] and [`PathCache::intern_batch`]
//! return the ID whose view equals `split(path bytes, delimiter)`.
//! `PathCache::lemma_id_eq_bytes` proves that returned IDs are equal iff their exact
//! path bytes are equal, within one cache. Existing IDs never invalidate.
//!
//! Splitting is leftmost and non-overlapping, preserving empty components:
//! `"" -> [""]`, `"/a" -> ["", "a"]`, `"a/" -> ["a", ""]`,
//! `"a//b" -> ["a", "", "b"]`, and `"a:::b" -> ["a", ":b"]` with `"::"`.
//! Leading delimiters count: `/home/foo/bar` creates four nodes. No normalization
//! occurs; `/a` differs from `a`, and `::std` differs from `std`.
//!
//! Empty delimiters return [`AllocErr::Capacity`]. Node capacity includes the root;
//! byte capacity stores component bytes. Arena exhaustion returns
//! [`AllocErr::Exhausted`] and retains already-created prefix nodes. If a parent
//! allocation fails after a component was stored, the orphan tail is never indexed;
//! further new edges return `Exhausted`, while existing paths remain usable.
//! Heap-side index, memo, delimiter, and scratch allocations use the global allocator
//! and can abort on OOM. Call [`PathCache::free`]: there is no `Drop`, so dropping
//! without freeing leaks the two arena chunks. Component access returns bytes.
//!
//! # Complexity
//! Per-component hash-table lookup is expected O(1), including byte hashing and
//! comparison costs. Scanning is O(n) for a fixed delimiter (O(n*m) worst case for
//! n path bytes and m delimiter bytes). LRU hits still hash/compare O(n) bytes,
//! but do not walk the trie or allocate. Batch walks resume at the deepest component
//! boundary shared with the previous path, and neither consult nor fill the LRU.
//! A zero memo capacity is rounded up to one. Fixed-seed hashing is not hardened
//! against adversarial hash flooding.
//!
//! # Trust inventory
//! * `key` assumes `foldhash::fast::FixedState` with a constant seed computes a pure,
//!   deterministic hash of the parent index and component bytes; collision freedom
//!   is neither assumed nor needed.
//! * Three `EdgeTable` external bodies assume `hashbrown::HashTable` creation is
//!   empty, lookup finds exactly a stored matching edge under the supplied hash,
//!   and insertion adds the pair. Rehashing uses the stored hash; lookup compares
//!   both parent and arena bytes, including safe out-of-range `get` behavior.
//! * Three `Memo` external bodies assume `lru::LruCache` behaves as a map: creation
//!   is empty, `get` returns exactly the equal key's value without changing map
//!   contents, and `put` installs the key/value and may only evict other keys.
//!   Cache invariants verify that every memoized ID is correct for its key.
//! * Bumpus trusts its `try_allocate`, `slice_ref`, and `Layout` bridges; this crate
//!   also relies on vstd axioms and standard-library specifications.
//!
//! Verification uses Verus `0.2026.10.04.426d8b0`, Rust `1.98.1`, and the same
//! `vstd =0.0.0-2026-09-06-0133` pin as bumpus. Run `cargo verus verify` without
//! `--check-toolchain`: that check rejects the older vstd pin, not the proofs.
extern crate alloc;
use alloc::vec::Vec;
use alloc::boxed::Box;
use core::hash::{BuildHasher, Hasher};
use core::num::NonZeroUsize;
use hashbrown::HashTable;
use verus_bumpalo::{SliceArena, TypedArena};
pub use verus_bumpalo::AllocErr;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::string::StringSliceAdditionalSpecFns;

verus! {
/// Leftmost, non-overlapping delimiter split, including empty components.
pub open spec fn split_from(s: Seq<u8>, d: Seq<u8>, start: int, i: int) -> Seq<Seq<u8>>
    decreases s.len() - i,
{
    if d.len() == 0 || i < 0 || start > i { seq![s] }
    else if s.len() - i < d.len() { seq![s.subrange(start, s.len() as int)] }
    else if s.subrange(i, i + d.len()) == d {
        seq![s.subrange(start, i)] + split_from(s, d, i + d.len(), i + d.len())
    } else { split_from(s, d, start, i + 1) }
}

pub open spec fn split(s: Seq<u8>, d: Seq<u8>) -> Seq<Seq<u8>> {
    split_from(s, d, 0, 0)
}

pub open spec fn join(parts: Seq<Seq<u8>>, d: Seq<u8>) -> Seq<u8>
    decreases parts.len(),
{
    if parts.len() == 0 { Seq::empty() }
    else if parts.len() == 1 { parts[0] }
    else { parts[0] + d + join(parts.drop_first(), d) }
}

proof fn lemma_join_split_from(s: Seq<u8>, d: Seq<u8>, start: int, i: int)
    requires d.len() > 0, 0 <= start <= i <= s.len(),
    ensures
        split_from(s, d, start, i).len() >= 1,
        join(split_from(s, d, start, i), d) == s.subrange(start, s.len() as int),
    decreases s.len() - i,
{
    if s.len() - i < d.len() {
    } else if s.subrange(i, i + d.len()) == d {
        lemma_join_split_from(s, d, i + d.len(), i + d.len());
        let rest = split_from(s, d, i + d.len(), i + d.len());
        assert((seq![s.subrange(start, i)] + rest).drop_first() =~= rest);
        assert(s.subrange(start, i) + d + s.subrange(i + d.len(), s.len() as int)
            =~= s.subrange(start, s.len() as int));
    } else {
        lemma_join_split_from(s, d, start, i + 1);
    }
}

pub proof fn lemma_split_injective(a: Seq<u8>, b: Seq<u8>, d: Seq<u8>)
    requires d.len() > 0, split(a, d) == split(b, d),
    ensures a == b,
{
    lemma_join_split_from(a, d, 0, 0);
    lemma_join_split_from(b, d, 0, 0);
    assert(a.subrange(0, a.len() as int) =~= a);
    assert(b.subrange(0, b.len() as int) =~= b);
}

/// Deterministic edge hash; byte comparison, not collision freedom, gives correctness.
pub uninterp spec fn spec_key(parent: u32, comp: Seq<u8>) -> u64;

const HASH_SEED: u64 = 0x9e37_79b9_7f4a_7c15;

#[verifier::external_body]
fn key(parent: u32, comp: &[u8]) -> (k: u64)
    ensures k == spec_key(parent, comp@),
{
    let mut h = foldhash::fast::FixedState::with_seed(HASH_SEED).build_hasher();
    h.write_u32(parent);
    h.write(comp);
    h.finish()
}

const INDEX_CAPACITY: usize = 1 << 12;

#[verifier::external_body]
struct EdgeTable { t: HashTable<(u64, u32)> }

impl View for EdgeTable {
    type V = Set<(u64, u32)>;
    uninterp spec fn view(&self) -> Set<(u64, u32)>;
}

impl EdgeTable {
    #[verifier::external_body]
    fn new() -> (t: EdgeTable)
        ensures t@ == Set::<(u64, u32)>::empty(),
    { EdgeTable { t: HashTable::with_capacity(INDEX_CAPACITY) } }

    #[verifier::external_body]
    fn find(&self, h: u64, parent: u32, comp: &[u8], parents: &TypedArena<u32>, comps: &SliceArena<u8>) -> (r: Option<u32>)
        ensures
            r matches Some(u) ==> self@.contains((h, u)) && (u as int) < parents@.len() && (u as int) < comps@.len()
                && parents@[u as int] == parent && comps@[u as int] == comp@,
            r is None ==> forall|u: u32| #[trigger] self@.contains((h, u)) && (u as int) < parents@.len() && (u as int) < comps@.len()
                ==> !(parents@[u as int] == parent && comps@[u as int] == comp@),
    {
        self.t.find(h, |&(hh, u)| hh == h
                && parents.get(u as usize).copied() == Some(parent)
                && comps.get(u as usize) == Some(comp))
            .map(|&(_, u)| u)
    }

    #[verifier::external_body]
    fn insert(&mut self, h: u64, u: u32)
        ensures final(self)@ == old(self)@.insert((h, u)),
    { self.t.insert_unique(h, (h, u), |&(hh, _)| hh); }
}

#[verifier::external_body]
pub struct Memo { inner: lru::LruCache<Box<[u8]>, u32> }

impl View for Memo {
    type V = Map<Seq<u8>, u32>;
    uninterp spec fn view(&self) -> Map<Seq<u8>, u32>;
}

impl Memo {
    #[verifier::external_body]
    fn new(cap: usize) -> (m: Memo)
        ensures m@ == Map::<Seq<u8>, u32>::empty(),
    { Memo { inner: lru::LruCache::new(NonZeroUsize::new(if cap == 0 { 1 } else { cap }).unwrap()) } }

    #[verifier::external_body]
    fn get(&mut self, s: &[u8]) -> (r: Option<u32>)
        ensures final(self)@ == old(self)@,
            r == if old(self)@.contains_key(s@) { Some(old(self)@[s@]) } else { None::<u32> },
    { self.inner.get(s).copied() }

    #[verifier::external_body]
    fn put(&mut self, s: &[u8], id: u32)
        ensures final(self)@.contains_key(s@) && final(self)@[s@] == id,
            forall|k: Seq<u8>| #[trigger] final(self)@.contains_key(k) ==> k == s@
                || (old(self)@.contains_key(k) && final(self)@[k] == old(self)@[k]),
    { self.inner.put(Box::from(s), id); }
}

/// Dense cache-local identity. Zero is the root sentinel, never returned by interning.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PathId(pub u64);

pub const DEFAULT_MAX_NODES: usize = 1 << 20;
pub const DEFAULT_MAX_BYTES: usize = 1 << 24;
pub const DEFAULT_MEMO_ENTRIES: usize = 1 << 12;

pub struct PathCache {
    delim: Vec<u8>,
    parents: TypedArena<u32>,
    comps: SliceArena<u8>,
    index: EdgeTable,
    memo: Memo,
}

spec fn comps_of(parents: Seq<u32>, comps: Seq<Seq<u8>>, id: int) -> Seq<Seq<u8>>
    decreases id,
{
    if id <= 0 || id >= parents.len() || parents[id] as int >= id { Seq::empty() }
    else { comps_of(parents, comps, parents[id] as int).push(comps[id]) }
}

impl View for PathCache {
    type V = Seq<Seq<Seq<u8>>>;
    closed spec fn view(&self) -> Seq<Seq<Seq<u8>>> {
        Seq::new(self.parents@.len(), |i: int| comps_of(self.parents@, self.comps@, i))
    }
}

impl PathCache {
    pub closed spec fn delim(&self) -> Seq<u8> { self.delim@ }

    pub closed spec fn inv(&self) -> bool {
        &&& self.delim@.len() > 0
        &&& 1 <= self.parents@.len() <= u32::MAX as int
        &&& self.parents@.len() <= self.comps@.len()
        &&& self.parents@[0] == 0 && self.comps@[0] == Seq::<u8>::empty()
        &&& forall|i: int| 1 <= i < self.parents@.len() ==> (#[trigger] self.parents@[i]) < i
        &&& forall|i: int, j: int| 1 <= i < self.parents@.len() && 1 <= j < self.parents@.len()
            && self.parents@[i] == self.parents@[j] && self.comps@[i] == self.comps@[j] ==> i == j
        &&& forall|i: int| 1 <= i < self.parents@.len() ==>
            self.index@.contains((spec_key(self.parents@[i], self.comps@[i]), i as u32))
        &&& forall|h: u64, u: u32| #[trigger] self.index@.contains((h, u)) ==> 1 <= u < self.parents@.len()
        &&& forall|k: Seq<u8>| #[trigger] self.memo@.contains_key(k) ==>
            1 <= self.memo@[k] < self.parents@.len() && self@[self.memo@[k] as int] == split(k, self.delim@)
    }

    pub proof fn lemma_injective(&self, i: int, j: int)
        requires self.inv(), 0 <= i < self@.len(), 0 <= j < self@.len(), self@[i] == self@[j],
        ensures i == j,
        decreases i + j,
    {
        if i == 0 {
            if j > 0 { lemma_nonroot_len(self.parents@, self.comps@, j); }
        } else if j == 0 {
            lemma_nonroot_len(self.parents@, self.comps@, i);
        } else {
            let pi = self.parents@[i] as int;
            let pj = self.parents@[j] as int;
            assert(self@[i].last() == self.comps@[i]);
            assert(self@[j].last() == self.comps@[j]);
            assert(self@[i].drop_last() =~= self@[pi]);
            assert(self@[j].drop_last() =~= self@[pj]);
            self.lemma_injective(pi, pj);
        }
    }

    pub proof fn lemma_id_eq(&self, i: PathId, j: PathId)
        requires self.inv(), 1 <= i.0 < self@.len(), 1 <= j.0 < self@.len(),
        ensures (i == j) <==> (self@[i.0 as int] == self@[j.0 as int]),
    {
        if self@[i.0 as int] == self@[j.0 as int] {
            self.lemma_injective(i.0 as int, j.0 as int);
        }
    }

    pub proof fn lemma_id_eq_bytes(&self, a: Seq<u8>, ia: PathId, b: Seq<u8>, ib: PathId)
        requires self.inv(), 1 <= ia.0 < self@.len(), 1 <= ib.0 < self@.len(),
            self@[ia.0 as int] == split(a, self.delim()), self@[ib.0 as int] == split(b, self.delim()),
        ensures (ia == ib) <==> (a == b),
    {
        self.lemma_id_eq(ia, ib);
        if ia == ib { lemma_split_injective(a, b, self.delim()); }
    }
}

proof fn lemma_comps_of_prefix(p1: Seq<u32>, c1: Seq<Seq<u8>>, p2: Seq<u32>, c2: Seq<Seq<u8>>, id: int)
    requires p1.is_prefix_of(p2), c1.is_prefix_of(c2), p1.len() <= c1.len(), 0 <= id < p1.len(),
    ensures comps_of(p2, c2, id) == comps_of(p1, c1, id),
    decreases id,
{
    assert(p1[id] == p2[id]);
    if id > 0 && p1[id] < id {
        lemma_comps_of_prefix(p1, c1, p2, c2, p1[id] as int);
    }
}

proof fn lemma_nonroot_len(p: Seq<u32>, c: Seq<Seq<u8>>, id: int)
    requires 1 <= id < p.len(), forall|i: int| 1 <= i < p.len() ==> (#[trigger] p[i]) < i,
    ensures comps_of(p, c, id).len() >= 1,
{
}

proof fn lemma_view_prefix(c1: PathCache, c2: PathCache)
    requires c1.parents@.is_prefix_of(c2.parents@), c1.comps@.is_prefix_of(c2.comps@), c1.parents@.len() <= c1.comps@.len(),
    ensures c1@.is_prefix_of(c2@),
{
    assert forall|i: int| 0 <= i < c1@.len() implies c1@[i] == c2@[i] by {
        lemma_comps_of_prefix(c1.parents@, c1.comps@, c2.parents@, c2.comps@, i);
    }
    assert(c1@ =~= c2@.subrange(0, c1@.len() as int));
}

impl PathCache {
    fn find(&self, parent: u32, comp: &[u8], h: u64) -> (r: Option<u32>)
        requires self.inv(), h == spec_key(parent, comp@),
        ensures
            r matches Some(u) ==> 1 <= u < self@.len() && self.parents@[u as int] == parent && self.comps@[u as int] == comp@,
            r is None ==> forall|u: int| 1 <= u < self@.len() ==> !(self.parents@[u] == parent && self.comps@[u] == comp@),
    {
        let r = self.index.find(h, parent, comp, &self.parents, &self.comps);
        proof {
            if r is None {
                assert forall|u: int| 1 <= u < self@.len() && self.parents@[u] == parent && self.comps@[u] == comp@
                    implies false by {
                    assert(self.index@.contains((spec_key(self.parents@[u], self.comps@[u]), u as u32)));
                    assert(u as u32 as int == u);
                }
            }
        }
        r
    }

    fn insert(&mut self, parent: u32, comp: &[u8], h: u64) -> (r: Result<u32, AllocErr>)
        requires old(self).inv(), h == spec_key(parent, comp@), parent < old(self)@.len(),
            forall|u: int| 1 <= u < old(self)@.len() ==> !(old(self).parents@[u] == parent && old(self).comps@[u] == comp@),
        ensures final(self).inv(), final(self).delim() == old(self).delim(), old(self)@.is_prefix_of(final(self)@),
            final(self).memo@ == old(self).memo@,
            r matches Ok(id) ==> id as int == old(self)@.len() && final(self)@.len() == old(self)@.len() + 1
                && final(self)@[id as int] == old(self)@[parent as int].push(comp@),
            r is Err ==> final(self)@ == old(self)@,
    {
        let ghost before = *self;
        // A failed parent push leaves a component tail. Never reuse its index for other bytes.
        if self.parents.len() >= u32::MAX as usize || self.comps.len() != self.parents.len() {
            return Err(AllocErr::Exhausted);
        }
        match self.comps.try_push(comp) {
            Err(e) => return Err(e),
            Ok(_) => {},
        }
        proof {
            assert(before.comps@.is_prefix_of(self.comps@));
            lemma_view_prefix(before, *self);
        }
        let i = match self.parents.try_push(parent) {
            Err(e) => {
                proof { self.lemma_memo_preserved(before); }
                return Err(e);
            },
            Ok(i) => i,
        };
        let id = i as u32;
        self.index.insert(h, id);
        proof {
            assert(before.parents@.is_prefix_of(self.parents@));
            lemma_view_prefix(before, *self);
            assert forall|j: int| 1 <= j < self.parents@.len() implies
                self.index@.contains((spec_key(self.parents@[j], self.comps@[j]), j as u32)) by {
                if j < i {
                    assert(before.index@.contains((spec_key(before.parents@[j], before.comps@[j]), j as u32)));
                }
            }
            self.lemma_memo_preserved(before);
        }
        Ok(id)
    }

    proof fn lemma_memo_preserved(&self, before: PathCache)
        requires before.inv(), before@.is_prefix_of(self@), self.delim() == before.delim(), self.memo@ == before.memo@,
        ensures forall|k: Seq<u8>| #[trigger] self.memo@.contains_key(k) ==>
            1 <= self.memo@[k] < self.parents@.len() && self@[self.memo@[k] as int] == split(k, self.delim@),
    {
        assert forall|k: Seq<u8>| #[trigger] self.memo@.contains_key(k) implies
            1 <= self.memo@[k] < self.parents@.len() && self@[self.memo@[k] as int] == split(k, self.delim@) by {
            assert(before@[before.memo@[k] as int] == self@[before.memo@[k] as int]);
        }
    }

    fn find_or_insert(&mut self, parent: u32, comp: &[u8]) -> (r: Result<u32, AllocErr>)
        requires old(self).inv(), parent < old(self)@.len(),
        ensures final(self).inv(), final(self).delim() == old(self).delim(), old(self)@.is_prefix_of(final(self)@),
            final(self).memo@ == old(self).memo@,
            r matches Ok(id) ==> 1 <= id < final(self)@.len()
                && final(self)@[id as int] == old(self)@[parent as int].push(comp@),
    {
        let h = key(parent, comp);
        match self.find(parent, comp, h) {
            Some(u) => Ok(u),
            None => self.insert(parent, comp, h),
        }
    }
}

spec fn scanning(s: Seq<u8>, d: Seq<u8>, read: int, start: int, i: int, prefix: Seq<Seq<u8>>) -> bool {
    forall|t: Seq<u8>| t.len() >= read && t.subrange(0, read) == s.subrange(0, read)
        ==> #[trigger] split(t, d) == prefix + split_from(t, d, start, i)
}

spec fn resumes(c: PathCache, s: Seq<u8>, off: int, node: int) -> bool {
    &&& 0 <= node < c@.len() && 0 <= off <= s.len()
    &&& scanning(s, c.delim(), off, off, off, c@[node])
}

proof fn lemma_resumes_prefix(c1: PathCache, c2: PathCache, s: Seq<u8>, off: int, node: int)
    requires resumes(c1, s, off, node), c1@.is_prefix_of(c2@), c1.delim() == c2.delim(),
    ensures resumes(c2, s, off, node),
{}

proof fn lemma_resumes_root(c: PathCache, s: Seq<u8>)
    requires c.inv(),
    ensures resumes(c, s, 0, 0),
{
    assert(c@[0] == Seq::<Seq<u8>>::empty());
    assert forall|t: Seq<u8>| t.len() >= 0 && t.subrange(0, 0) == s.subrange(0, 0)
        implies #[trigger] split(t, c.delim()) == c@[0] + split_from(t, c.delim(), 0, 0) by {
        assert(Seq::<Seq<u8>>::empty() + split(t, c.delim()) =~= split(t, c.delim()));
    }
}

proof fn lemma_resumes_transfer(c: PathCache, prev: Seq<u8>, s: Seq<u8>, l: int, off: int, node: int)
    requires resumes(c, prev, off, node), off <= l <= s.len(), l <= prev.len(),
        prev.subrange(0, l) == s.subrange(0, l),
    ensures resumes(c, s, off, node),
{
    assert(prev.subrange(0, off) =~= prev.subrange(0, l).subrange(0, off));
    assert(s.subrange(0, off) =~= s.subrange(0, l).subrange(0, off));
}

proof fn lemma_agree(s: Seq<u8>, t: Seq<u8>, n: int, a: int, b: int)
    requires 0 <= a <= b <= n <= s.len(), n <= t.len(), t.subrange(0, n) == s.subrange(0, n),
    ensures t.subrange(a, b) == s.subrange(a, b),
{
    assert(t.subrange(a, b) =~= t.subrange(0, n).subrange(a, b));
    assert(s.subrange(a, b) =~= s.subrange(0, n).subrange(a, b));
}

proof fn lemma_step_nomatch(s: Seq<u8>, d: Seq<u8>, read: int, start: int, i: int, prefix: Seq<Seq<u8>>)
    requires d.len() > 0, 0 <= start <= i, i + d.len() <= s.len(), 0 <= read <= i + d.len(),
        scanning(s, d, read, start, i, prefix), s.subrange(i, i + d.len()) != d,
    ensures scanning(s, d, i + d.len(), start, i + 1, prefix),
{
    assert forall|t: Seq<u8>| t.len() >= i + d.len() && t.subrange(0, i + d.len()) == s.subrange(0, i + d.len())
        implies #[trigger] split(t, d) == prefix + split_from(t, d, start, i + 1) by {
        lemma_agree(s, t, i + d.len(), 0, read);
        lemma_agree(s, t, i + d.len(), i, i + d.len());
        assert(split(t, d) == prefix + split_from(t, d, start, i));
    }
}

proof fn lemma_step_match(s: Seq<u8>, d: Seq<u8>, read: int, start: int, i: int, prefix: Seq<Seq<u8>>)
    requires d.len() > 0, 0 <= start <= i, i + d.len() <= s.len(), 0 <= read <= i + d.len(),
        scanning(s, d, read, start, i, prefix), s.subrange(i, i + d.len()) == d,
    ensures scanning(s, d, i + d.len(), i + d.len(), i + d.len(), prefix.push(s.subrange(start, i))),
{
    assert forall|t: Seq<u8>| t.len() >= i + d.len() && t.subrange(0, i + d.len()) == s.subrange(0, i + d.len())
        implies #[trigger] split(t, d) == prefix.push(s.subrange(start, i)) + split_from(t, d, i + d.len(), i + d.len()) by {
        lemma_agree(s, t, i + d.len(), 0, read);
        lemma_agree(s, t, i + d.len(), i, i + d.len());
        lemma_agree(s, t, i + d.len(), start, i);
        assert(split(t, d) == prefix + split_from(t, d, start, i));
        let rest = split_from(t, d, i + d.len(), i + d.len());
        assert(prefix + (seq![s.subrange(start, i)] + rest) =~= prefix.push(s.subrange(start, i)) + rest);
    }
}

fn match_at(s: &[u8], i: usize, d: &[u8]) -> (b: bool)
    requires d@.len() >= 1, i <= s@.len(), s@.len() - i >= d@.len(),
    ensures b == (s@.subrange(i as int, i + d@.len()) == d@),
{
    let _n = s.len(); // Exposes the machine-sized slice bound to the verifier.
    let dl = d.len();
    if dl == 1 {
        proof { assert(s@.subrange(i as int, i + d@.len()) =~= seq![s@[i as int]]); assert(d@ =~= seq![d@[0]]); }
        s[i] == d[0]
    } else {
        let sub = &s[i..i + dl];
        let equal = sub == d;
        proof { if equal { assert(sub@ =~= d@); } }
        equal
    }
}

impl PathCache {
    #[verifier::spinoff_prover]
    fn scan(&mut self, s: &[u8], off: usize, node: u32, track: bool, stack: &mut Vec<(usize, u32)>) -> (r: Result<u32, AllocErr>)
        requires old(self).inv(), resumes(*old(self), s@, off as int, node as int),
            forall|a: int| 0 <= a < old(stack)@.len() ==> (#[trigger] old(stack)@[a]).0 <= off,
            forall|a: int, b: int| 0 <= a < b < old(stack)@.len() ==> (#[trigger] old(stack)@[a]).0 < (#[trigger] old(stack)@[b]).0,
        ensures final(self).inv(), final(self).delim() == old(self).delim(), old(self)@.is_prefix_of(final(self)@),
            final(self).memo@ == old(self).memo@,
            old(stack)@.is_prefix_of(final(stack)@), !track ==> final(stack)@ == old(stack)@,
            forall|a: int| old(stack)@.len() <= a < final(stack)@.len() ==>
                resumes(*final(self), s@, (#[trigger] final(stack)@[a]).0 as int, final(stack)@[a].1 as int),
            forall|a: int, b: int| 0 <= a < b < final(stack)@.len() ==>
                (#[trigger] final(stack)@[a]).0 < (#[trigger] final(stack)@[b]).0,
            r matches Ok(id) ==> 1 <= id < final(self)@.len() && final(self)@[id as int] == split(s@, final(self).delim()),
    {
        let n = s.len();
        let dl = self.delim.len();
        let mut cur = node;
        let mut start = off;
        let mut i = off;
        let ghost mut read: int = off as int;
        loop
            invariant
                self.inv(), self.delim() == old(self).delim(), old(self)@.is_prefix_of(self@), self.memo@ == old(self).memo@,
                n == s@.len(), dl == self.delim@.len(),
                off <= start <= i <= n, i <= read <= n, read <= i + dl - 1,
                cur < self@.len(), scanning(s@, self.delim(), read, start as int, i as int, self@[cur as int]),
                old(stack)@.is_prefix_of(stack@), !track ==> stack@ == old(stack)@,
                forall|a: int| old(stack)@.len() <= a < stack@.len() ==>
                    resumes(*self, s@, (#[trigger] stack@[a]).0 as int, stack@[a].1 as int),
                forall|a: int, b: int| 0 <= a < b < stack@.len() ==> (#[trigger] stack@[a]).0 < (#[trigger] stack@[b]).0,
                forall|a: int| 0 <= a < stack@.len() ==> (#[trigger] stack@[a]).0 <= start,
            decreases n - i,
        {
            let ghost before = *self;
            if n - i < dl {
                proof {
                    assert(split(s@, self.delim()) == self@[cur as int] + split_from(s@, self.delim(), start as int, i as int));
                    assert(self@[cur as int] + seq![s@.subrange(start as int, n as int)]
                        =~= self@[cur as int].push(s@.subrange(start as int, n as int)));
                }
                let result = self.find_or_insert(cur, &s[start..n]);
                proof {
                    assert forall|a: int| old(stack)@.len() <= a < stack@.len() implies
                        resumes(*self, s@, (#[trigger] stack@[a]).0 as int, stack@[a].1 as int) by {
                        lemma_resumes_prefix(before, *self, s@, stack@[a].0 as int, stack@[a].1 as int);
                    }
                }
                return result;
            }
            if match_at(s, i, self.delim.as_slice()) {
                proof { lemma_step_match(s@, self.delim(), read, start as int, i as int, self@[cur as int]); }
                let result = self.find_or_insert(cur, &s[start..i]);
                proof {
                    assert forall|a: int| old(stack)@.len() <= a < stack@.len() implies
                        resumes(*self, s@, (#[trigger] stack@[a]).0 as int, stack@[a].1 as int) by {
                        lemma_resumes_prefix(before, *self, s@, stack@[a].0 as int, stack@[a].1 as int);
                    }
                }
                let next = match result { Ok(id) => id, Err(e) => return Err(e) };
                proof { assert(resumes(*self, s@, i + dl, next as int)); }
                if track { stack.push((i + dl, next)); }
                start = i + dl;
                i = start;
                cur = next;
                proof { read = i as int; }
            } else {
                proof { lemma_step_nomatch(s@, self.delim(), read, start as int, i as int, self@[cur as int]); }
                i += 1;
                proof { read = i as int + dl as int - 1; }
            }
        }
    }
}

fn lcp(a: &[u8], b: &[u8]) -> (l: usize)
    ensures l <= a@.len(), l <= b@.len(), a@.subrange(0, l as int) == b@.subrange(0, l as int),
{
    let mut l = 0;
    while l < a.len() && l < b.len()
        invariant l <= a@.len(), l <= b@.len(), a@.subrange(0, l as int) == b@.subrange(0, l as int),
        decreases a@.len() - l,
    {
        if a[l] != b[l] { break; }
        proof { assert(a@.subrange(0, l + 1) =~= b@.subrange(0, l + 1)); }
        l += 1;
    }
    l
}

impl PathCache {
    pub closed spec fn memo_empty(&self) -> bool { self.memo@ == Map::<Seq<u8>, u32>::empty() }

    /// Creates a cache with the default node, byte, and memo capacities.
    pub fn new(delim: &str) -> (r: Result<PathCache, AllocErr>)
        ensures r matches Ok(c) ==> c.inv() && c@.len() == 1 && c.delim() == delim.spec_bytes() && c.memo_empty(),
            delim.spec_bytes().len() == 0 ==> r == Err(AllocErr::Capacity),
    {
        Self::with_capacity(delim, DEFAULT_MAX_NODES, DEFAULT_MAX_BYTES, DEFAULT_MEMO_ENTRIES)
    }

    /// Capacities include the root. Empty delimiters and invalid capacities return `Capacity`.
    /// A zero memo capacity is rounded up to one entry.
    pub fn with_capacity(delim: &str, max_nodes: usize, max_bytes: usize, memo_entries: usize) -> (r: Result<PathCache, AllocErr>)
        ensures r matches Ok(c) ==> c.inv() && c@.len() == 1 && c.delim() == delim.spec_bytes() && c.memo_empty(),
            delim.spec_bytes().len() == 0 ==> r == Err(AllocErr::Capacity),
    {
        let d = delim.as_bytes();
        if d.len() == 0 { return Err(AllocErr::Capacity); }
        let node_bytes = match max_nodes.checked_mul(4) { Some(b) => b, None => return Err(AllocErr::Capacity) };
        let mut parents = match TypedArena::<u32>::with_capacity(node_bytes) { Ok(a) => a, Err(e) => return Err(e) };
        let mut comps = match SliceArena::<u8>::with_capacity(max_bytes) {
            Ok(a) => a,
            Err(e) => { parents.free(); return Err(e); },
        };
        match parents.try_push(0) {
            Ok(_) => {},
            Err(e) => { parents.free(); comps.free(); return Err(e); },
        }
        let empty = Vec::<u8>::new();
        match comps.try_push(empty.as_slice()) {
            Ok(_) => {},
            Err(e) => { parents.free(); comps.free(); return Err(e); },
        }
        let mut delimiter = Vec::new();
        delimiter.extend_from_slice(d);
        let cache = PathCache { delim: delimiter, parents, comps, index: EdgeTable::new(), memo: Memo::new(memo_entries) };
        proof { assert(cache@ =~= seq![Seq::<Seq<u8>>::empty()]); }
        Ok(cache)
    }

    /// Interns exact path bytes. Failure preserves existing IDs and any newly created prefixes.
    pub fn intern(&mut self, path: &str) -> (r: Result<PathId, AllocErr>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).delim() == old(self).delim(), old(self)@.is_prefix_of(final(self)@),
            r matches Ok(id) ==> 1 <= id.0 < final(self)@.len() && final(self)@[id.0 as int] == split(path.spec_bytes(), final(self).delim()),
    {
        let s = path.as_bytes();
        if let Some(id) = self.memo.get(s) { return Ok(PathId(id as u64)); }
        let mut scratch: Vec<(usize, u32)> = Vec::new();
        proof { lemma_resumes_root(*self, s@); }
        match self.scan(s, 0, 0, false, &mut scratch) {
            Ok(id) => {
                let ghost before = *self;
                self.memo.put(s, id);
                proof {
                    assert forall|k: Seq<u8>| #[trigger] self.memo@.contains_key(k) implies
                        1 <= self.memo@[k] < self.parents@.len() && self@[self.memo@[k] as int] == split(k, self.delim@) by {
                        if k != s@ { assert(before.memo@.contains_key(k)); }
                    }
                }
                Ok(PathId(id as u64))
            },
            Err(e) => Err(e),
        }
    }

    /// Resumes each walk at its deepest shared component boundary. Does not use or fill the LRU.
    pub fn intern_batch(&mut self, paths: &[&str]) -> (r: Result<Vec<PathId>, AllocErr>)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).delim() == old(self).delim(), old(self)@.is_prefix_of(final(self)@),
            r matches Ok(ids) ==> ids@.len() == paths@.len()
                && forall|k: int| 0 <= k < ids@.len() ==> 1 <= (#[trigger] ids@[k]).0 < final(self)@.len()
                    && final(self)@[ids@[k].0 as int] == split(paths@[k].spec_bytes(), final(self).delim()),
    {
        let mut ids: Vec<PathId> = Vec::with_capacity(paths.len());
        let mut stack: Vec<(usize, u32)> = Vec::new();
        let mut k = 0;
        while k < paths.len()
            invariant
                self.inv(), self.delim() == old(self).delim(), old(self)@.is_prefix_of(self@),
                ids@.len() == k, k <= paths@.len(),
                forall|j: int| 0 <= j < k ==> 1 <= (#[trigger] ids@[j]).0 < self@.len()
                    && self@[ids@[j].0 as int] == split(paths@[j].spec_bytes(), self.delim()),
                k == 0 ==> stack@.len() == 0,
                k > 0 ==> forall|a: int| 0 <= a < stack@.len() ==>
                    resumes(*self, paths@[k - 1].spec_bytes(), (#[trigger] stack@[a]).0 as int, stack@[a].1 as int),
                forall|a: int, b: int| 0 <= a < b < stack@.len() ==> (#[trigger] stack@[a]).0 < (#[trigger] stack@[b]).0,
            decreases paths@.len() - k,
        {
            let s = paths[k].as_bytes();
            if k > 0 {
                let prev = paths[k - 1].as_bytes();
                let l = lcp(prev, s);
                while stack.len() > 0 && stack[stack.len() - 1].0 > l
                    invariant
                        self.inv(), l <= prev@.len(), l <= s@.len(), prev@.subrange(0, l as int) == s@.subrange(0, l as int),
                        forall|a: int| 0 <= a < stack@.len() ==>
                            resumes(*self, prev@, (#[trigger] stack@[a]).0 as int, stack@[a].1 as int),
                        forall|a: int, b: int| 0 <= a < b < stack@.len() ==> (#[trigger] stack@[a]).0 < (#[trigger] stack@[b]).0,
                    decreases stack@.len(),
                { stack.pop(); }
                proof {
                    assert forall|a: int| 0 <= a < stack@.len() implies
                        resumes(*self, s@, (#[trigger] stack@[a]).0 as int, stack@[a].1 as int) && stack@[a].0 <= l by {
                        if a < stack@.len() - 1 { assert(stack@[a].0 < stack@[stack@.len() - 1].0); }
                        lemma_resumes_transfer(*self, prev@, s@, l as int, stack@[a].0 as int, stack@[a].1 as int);
                    }
                }
            }
            let (off, node) = if stack.len() > 0 { stack[stack.len() - 1] } else { (0usize, 0u32) };
            proof {
                if stack@.len() == 0 { lemma_resumes_root(*self, s@); }
                assert forall|a: int| 0 <= a < stack@.len() implies (#[trigger] stack@[a]).0 <= off by {
                    if a < stack@.len() - 1 { assert(stack@[a].0 < stack@[stack@.len() - 1].0); }
                }
            }
            let ghost before = *self;
            let ghost old_stack = stack@;
            let id = match self.scan(s, off, node, true, &mut stack) { Ok(id) => id, Err(e) => return Err(e) };
            proof {
                assert forall|a: int| 0 <= a < old_stack.len() implies
                    resumes(*self, s@, (#[trigger] stack@[a]).0 as int, stack@[a].1 as int) by {
                    assert(stack@[a] == old_stack[a]);
                    lemma_resumes_prefix(before, *self, s@, old_stack[a].0 as int, old_stack[a].1 as int);
                }
                assert forall|j: int| 0 <= j < k implies
                    self@[ids@[j].0 as int] == before@[ids@[j].0 as int] by {};
            }
            ids.push(PathId(id as u64));
            k += 1;
        }
        Ok(ids)
    }

    /// Returns the preceding path, or `None` for a single-component path.
    /// Panics for an invalid ID. IDs from different caches must not be mixed.
    pub fn parent(&self, id: PathId) -> (p: Option<PathId>)
        requires self.inv(), 1 <= id.0 < self@.len(),
        ensures p matches Some(q) ==> 1 <= q.0 < id.0 && self@[q.0 as int] == self@[id.0 as int].drop_last(),
            p is None ==> self@[id.0 as int].len() == 1,
    {
        vstd::pervasive::runtime_assert(1 <= id.0 && id.0 < self.parents.len() as u64);
        let par = *self.parents.get(id.0 as usize).unwrap();
        proof { assert(self@[id.0 as int].drop_last() =~= self@[par as int]); }
        if par == 0 { None } else { Some(PathId(par as u64)) }
    }

    /// Borrows the final component. Panics for an invalid ID.
    pub fn component(&self, id: PathId) -> (c: &[u8])
        requires self.inv(), 1 <= id.0 < self@.len(),
        ensures c@ == self@[id.0 as int].last(),
    {
        vstd::pervasive::runtime_assert(1 <= id.0 && id.0 < self.parents.len() as u64);
        self.comps.get(id.0 as usize).unwrap()
    }

    /// Number of trie nodes, excluding the root; valid IDs are `1..=len()`.
    pub fn len(&self) -> (n: usize)
        requires self.inv(),
        ensures n == self@.len() - 1,
    { self.parents.len() - 1 }

    pub fn delimiter(&self) -> (d: &[u8])
        ensures d@ == self.delim(),
    { self.delim.as_slice() }

    /// Releases both arenas. Dropping without calling this leaks their chunks.
    pub fn free(self) { self.parents.free(); self.comps.free(); }
}
}
