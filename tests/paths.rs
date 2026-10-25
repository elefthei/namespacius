use namespacius::{AllocErr, PathCache, PathId};
use std::collections::HashMap;

#[test]
fn same_string_same_id() {
    let mut cache = PathCache::new("/").unwrap();
    assert_eq!(cache.len(), 0);
    assert_eq!(cache.delimiter(), b"/");
    let id = cache.intern("/home/foo/bar").unwrap();
    assert_ne!(id, PathId(0));
    assert_eq!(cache.intern("/home/foo/bar").unwrap(), id);
    assert_eq!(cache.len(), 4);
    cache.free();
}

#[test]
fn distinct_strings_distinct_ids() {
    let mut cache = PathCache::new("/").unwrap();
    let paths = ["/a/b", "a/b", "/a/b/", "/a//b", "", "/"];
    let ids: Vec<PathId> = paths.iter().map(|path| cache.intern(path).unwrap()).collect();
    for (i, &id) in ids.iter().enumerate() {
        assert_ne!(id, PathId(0));
        for j in 0..i {
            assert_ne!(id, ids[j], "{:?} and {:?}", paths[i], paths[j]);
        }
    }
    assert_eq!(cache.component(ids[4]), b"");
    assert_eq!(cache.parent(ids[4]), None);
    assert_eq!(cache.component(ids[5]), b"");
    assert_eq!(cache.parent(ids[5]), Some(ids[4]));
    cache.free();
}

#[test]
fn multibyte_delimiter() {
    let mut cache = PathCache::new("::").unwrap();
    let id = cache.intern("a:::b").unwrap();
    let parent = cache.parent(id).unwrap();
    assert_eq!(cache.len(), 2);
    assert_eq!(cache.component(id), b":b");
    assert_eq!(cache.component(parent), b"a");
    assert_eq!(cache.parent(parent), None);
    let memo_id = cache.intern("a:::b").unwrap();
    assert_eq!(memo_id, id);
    println!(
        "a:::b components={:?}, len={}, id={id:?}, memo_id={memo_id:?}",
        [cache.component(parent), cache.component(id)],
        cache.len()
    );
    let vector = cache.intern("std::vector").unwrap();
    assert_eq!(cache.intern("std::vector").unwrap(), vector);
    assert_ne!(cache.intern("std:::vector").unwrap(), vector);
    cache.free();

    // Adjacent paths share bytes inside a delimiter or inside the next component.
    let paths = [
        "a:::b", "a::b", "a::::b", "a::", "a", "", "::", ":::b",
        "a:::b", "é::猫", "é:::猫", "é::猫::", "é::犬",
    ];
    let mut batch = PathCache::new("::").unwrap();
    let mut single = PathCache::new("::").unwrap();
    let ids = batch.intern_batch(&paths).unwrap();
    let expected: Vec<PathId> = paths.iter().map(|path| single.intern(path).unwrap()).collect();
    assert_eq!(ids, expected);
    assert_eq!(batch.len(), single.len());
    for (&id, path) in ids.iter().zip(paths) {
        let mut parts = Vec::new();
        let mut current = Some(id);
        while let Some(node) = current {
            parts.push(batch.component(node));
            current = batch.parent(node);
        }
        parts.reverse();
        assert_eq!(parts, path.split("::").map(str::as_bytes).collect::<Vec<_>>());
    }
    let len = batch.len();
    assert_eq!(batch.intern_batch(&paths).unwrap(), ids);
    assert_eq!(batch.len(), len);
    batch.free();
    single.free();
}

#[test]
fn parent_component_roundtrip() {
    let mut cache = PathCache::new("/").unwrap();
    for path in ["/usr/lib/x", "/χρήστης/猫/🦀", "", "a//b/"] {
        let id = cache.intern(path).unwrap();
        let mut parts = Vec::new();
        let mut current = Some(id);
        while let Some(node) = current {
            parts.push(cache.component(node));
            current = cache.parent(node);
        }
        parts.reverse();
        assert_eq!(parts.join(cache.delimiter()), path.as_bytes());
        assert_eq!(parts, path.split('/').map(str::as_bytes).collect::<Vec<_>>());
    }
    cache.free();
}

#[test]
fn memo_hits_survive_eviction() {
    let mut cache = PathCache::with_capacity("/", 1 << 16, 1 << 20, 4).unwrap();
    let paths: Vec<String> = (0..10).map(|i| format!("p{i}")).collect();
    let ids: Vec<PathId> = paths.iter().map(|path| cache.intern(path).unwrap()).collect();
    assert_eq!(cache.len(), 10);
    for i in [0, 9, 1, 8, 2, 7, 3, 6, 4, 5, 0, 9, 0] {
        assert_eq!(cache.intern(&paths[i]).unwrap(), ids[i]);
        assert_eq!(cache.component(ids[i]), paths[i].as_bytes());
        assert_eq!(cache.parent(ids[i]), None);
    }
    assert_eq!(cache.len(), 10);
    cache.free();
}

#[test]
fn batch_matches_single() {
    let mut paths = Vec::with_capacity(300);
    for i in 0..10 {
        for j in 0..5 {
            for k in 0..6 {
                paths.push(format!("/r/d{i}/s{j}/f{k}"));
            }
        }
    }
    assert_eq!(paths.len(), 300);
    let refs: Vec<&str> = paths.iter().map(String::as_str).collect();
    let mut batch = PathCache::new("/").unwrap();
    let mut single = PathCache::new("/").unwrap();
    assert!(batch.intern_batch(&[]).unwrap().is_empty());
    assert_eq!(batch.len(), 0);
    let ids = batch.intern_batch(&refs).unwrap();
    let expected: Vec<PathId> = refs.iter().map(|path| single.intern(path).unwrap()).collect();
    assert_eq!(ids, expected);
    assert_eq!(batch.len(), single.len());
    let len = batch.len();
    assert_eq!(batch.intern_batch(&refs).unwrap(), ids);
    assert_eq!(batch.len(), len);
    for (path, &id) in refs.iter().zip(&ids) {
        assert_eq!(batch.intern(path).unwrap(), id);
    }
    assert_eq!(batch.len(), len);
    batch.free();
    single.free();
}

#[test]
fn batch_resume_correct_on_divergence() {
    let paths = ["a/b/c", "a/b", "a/bc/d", "a/", "a", "", "a/b/c"];
    let mut batch = PathCache::new("/").unwrap();
    let mut single = PathCache::new("/").unwrap();
    let ids = batch.intern_batch(&paths).unwrap();
    println!("batch_resume_correct_on_divergence IDs={ids:?}");
    let expected: Vec<PathId> = paths.iter().map(|path| single.intern(path).unwrap()).collect();
    assert_eq!(ids, expected);
    assert_eq!(ids[0], ids[6]);
    for i in 0..6 {
        for j in 0..i {
            assert_ne!(ids[i], ids[j], "{:?} and {:?}", paths[i], paths[j]);
        }
    }
    assert_eq!(batch.parent(ids[0]), Some(ids[1]));
    assert_eq!(batch.parent(ids[1]), Some(ids[4]));
    assert_eq!(batch.parent(ids[3]), Some(ids[4]));
    assert_eq!(batch.component(ids[3]), b"");
    assert_eq!(batch.parent(ids[5]), None);
    assert_eq!(batch.len(), single.len());
    batch.free();
    single.free();
}

#[test]
fn exhaustion() {
    assert!(matches!(PathCache::with_capacity("", 2, 64, 8), Err(AllocErr::Capacity)));
    assert!(matches!(PathCache::new(""), Err(AllocErr::Capacity)));
    let mut cache = PathCache::with_capacity("/", 2, 64, 8).unwrap();
    let a = cache.intern("a").unwrap();
    for path in ["b", "c", "b", "a/b", "d"] {
        assert!(matches!(cache.intern(path), Err(AllocErr::Exhausted)));
        assert_eq!(cache.len(), 1);
        assert_eq!(cache.intern("a").unwrap(), a);
        assert_eq!(cache.intern_batch(&["a", "a"]).unwrap(), vec![a, a]);
        assert_eq!(cache.component(a), b"a");
        assert_eq!(cache.parent(a), None);
    }
    cache.free();

    let mut bytes = PathCache::with_capacity("/", 16, 3, 1).unwrap();
    assert!(matches!(bytes.intern("a/b/cc"), Err(AllocErr::Exhausted)));
    assert_eq!(bytes.len(), 2);
    // Neither prefix was memoized by the failed call; both remain in the trie.
    let a = bytes.intern("a").unwrap();
    let ab = bytes.intern("a/b").unwrap();
    assert_eq!(bytes.parent(ab), Some(a));
    assert_eq!(bytes.component(ab), b"b");
    for _ in 0..3 {
        assert!(matches!(bytes.intern("a/b/cc"), Err(AllocErr::Exhausted)));
        assert_eq!(bytes.intern("a/b").unwrap(), ab);
        assert_eq!(bytes.len(), 2);
    }
    // Byte-allocation failure creates no orphan: the last byte is still usable.
    let abc = bytes.intern("a/b/c").unwrap();
    assert_eq!(bytes.parent(abc), Some(ab));
    assert_eq!(bytes.component(abc), b"c");
    assert!(matches!(bytes.intern("z"), Err(AllocErr::Exhausted)));
    assert_eq!(bytes.intern("a").unwrap(), a);
    assert_eq!(bytes.intern("a/b").unwrap(), ab);
    bytes.free();
}

#[test]
fn oracle_random() {
    let mut cache = PathCache::new("/").unwrap();
    let mut forward: HashMap<String, PathId> = HashMap::new();
    let mut reverse: HashMap<PathId, String> = HashMap::new();
    let mut state = 0x4d59_5df4_d0f3_3173_u64;
    for _ in 0..5_000 {
        state = state.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        let len = ((state >> 32) % 9) as usize;
        let mut path = String::with_capacity(len);
        for _ in 0..len {
            state = state.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            path.push([b'a', b'b', b'/'][((state >> 32) % 3) as usize] as char);
        }
        let id = cache.intern(&path).unwrap();
        assert_ne!(id, PathId(0));
        if let Some(previous) = forward.insert(path.clone(), id) {
            assert_eq!(id, previous, "same string changed ID: {path:?}");
        }
        if let Some(previous) = reverse.insert(id, path.clone()) {
            assert_eq!(path, previous, "distinct strings share {id:?}");
        }
    }
    assert_eq!(forward.len(), reverse.len());
    for (path, &id) in &forward {
        assert_eq!(reverse.get(&id), Some(path));
        assert_eq!(cache.intern(path).unwrap(), id);
    }
    cache.free();
}
