// Author: Shaobo He
// LeetCode 146: LRU Cache
//
// Functional-correctness proof of an LRU cache (we model the *behaviour*, not
// the O(1) time bound, which Dafny does not reason about).
//
// State is a `seq<(int,int)>` of (key,value) entries in most-recently-used-first
// order, with a class invariant that keys are distinct and the size never
// exceeds the capacity. `AsMapOf` reads the entries as an abstract map, and the
// operations are proved to behave as that map with LRU eviction:
//   * Get returns the map lookup (or -1) and moves the key to the front, leaving
//     the abstract map unchanged.
//   * Put updates the map at the key and moves it to the front; on overflow it
//     evicts exactly the least-recently-used entry (the back of the list).

// ---------------------------------------------------------------------------
// Pure layer: entries, their keys, and the abstract map
// ---------------------------------------------------------------------------

predicate Distinct(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

function Keys(e: seq<(int, int)>): seq<int>
  ensures |Keys(e)| == |e|
{
  if |e| == 0 then [] else [e[0].0] + Keys(e[1..])
}

lemma DistinctPrefix(s: seq<int>, n: int)
  requires 0 <= n <= |s|
  requires Distinct(s)
  ensures Distinct(s[..n])
{
}

lemma KeysIndex(e: seq<(int, int)>)
  ensures |Keys(e)| == |e|
  ensures forall i :: 0 <= i < |e| ==> Keys(e)[i] == e[i].0
{
  if |e| > 0 {
    KeysIndex(e[1..]);
  }
}

predicate DistinctKeys(e: seq<(int, int)>) {
  Distinct(Keys(e))
}

lemma DistinctKeysTail(e: seq<(int, int)>)
  requires |e| > 0 && DistinctKeys(e)
  ensures DistinctKeys(e[1..])
{
  KeysIndex(e);
  KeysIndex(e[1..]);
  assert Keys(e)[1..] == Keys(e[1..]);
}

lemma DistinctConsIntro(x: int, t: seq<int>)
  requires Distinct(t)
  requires x !in t
  ensures Distinct([x] + t)
{
  var s := [x] + t;
  forall i, j | 0 <= i < j < |s|
    ensures s[i] != s[j]
  {
    if i == 0 {
      assert s[j] == t[j - 1] && t[j - 1] in t;
    } else {
      assert s[i] == t[i - 1] && s[j] == t[j - 1];
    }
  }
}

lemma HeadNotInTail(e: seq<(int, int)>)
  requires |e| > 0 && DistinctKeys(e)
  ensures e[0].0 !in Keys(e[1..])
{
  KeysIndex(e);
  if e[0].0 in Keys(e[1..]) {
    var j :| 0 <= j < |Keys(e[1..])| && Keys(e[1..])[j] == e[0].0;
    assert Keys(e)[j + 1] == Keys(e[1..])[j];
    assert Keys(e)[0] == e[0].0;
  }
}

function AsMapOf(e: seq<(int, int)>): map<int, int> {
  if |e| == 0 then map[] else AsMapOf(e[1..])[e[0].0 := e[0].1]
}

lemma AsMapMembership(e: seq<(int, int)>, k: int)
  ensures k in AsMapOf(e) <==> k in Keys(e)
{
  if |e| > 0 {
    AsMapMembership(e[1..], k);
  }
}

// With distinct keys, the abstract map returns each entry's own value.
lemma AsMapValueAt(e: seq<(int, int)>, i: int)
  requires DistinctKeys(e)
  requires 0 <= i < |e|
  ensures e[i].0 in AsMapOf(e)
  ensures AsMapOf(e)[e[i].0] == e[i].1
{
  KeysIndex(e);
  if i > 0 {
    assert Keys(e)[0] == e[0].0 && Keys(e)[i] == e[i].0;
    assert e[i].0 != e[0].0;
    DistinctKeysTail(e);
    AsMapValueAt(e[1..], i - 1);
    AsMapMembership(e[1..], e[i].0);
  }
}

// Value stored at a present key.
function ValueOf(e: seq<(int, int)>, k: int): int
  requires k in Keys(e)
{
  if e[0].0 == k then e[0].1 else ValueOf(e[1..], k)
}

lemma ValueOfIsMap(e: seq<(int, int)>, k: int)
  requires DistinctKeys(e)
  requires k in Keys(e)
  ensures k in AsMapOf(e) && AsMapOf(e)[k] == ValueOf(e, k)
{
  AsMapMembership(e, k);
  if e[0].0 != k {
    DistinctKeysTail(e);
    ValueOfIsMap(e[1..], k);
  }
}

// ---------------------------------------------------------------------------
// RemoveKey: drop the entry with a given key
// ---------------------------------------------------------------------------

function RemoveKey(e: seq<(int, int)>, k: int): seq<(int, int)> {
  if |e| == 0 then []
  else if e[0].0 == k then RemoveKey(e[1..], k)
  else [e[0]] + RemoveKey(e[1..], k)
}

lemma RemoveKeyKeys(e: seq<(int, int)>, k: int)
  ensures k !in Keys(RemoveKey(e, k))
  ensures forall j :: j in Keys(RemoveKey(e, k)) ==> j in Keys(e) && j != k
{
  if |e| > 0 {
    RemoveKeyKeys(e[1..], k);
  }
}

lemma RemoveKeyDistinct(e: seq<(int, int)>, k: int)
  requires DistinctKeys(e)
  ensures DistinctKeys(RemoveKey(e, k))
{
  if |e| > 0 {
    KeysIndex(e);
    DistinctKeysTail(e);
    RemoveKeyDistinct(e[1..], k);
    if e[0].0 != k {
      // Keys(RemoveKey(e,k)) == [e[0].0] + Keys(RemoveKey(e[1..],k))
      assert RemoveKey(e, k) == [e[0]] + RemoveKey(e[1..], k);
      assert Keys(RemoveKey(e, k)) == [e[0].0] + Keys(RemoveKey(e[1..], k));
      RemoveKeyKeys(e[1..], k);
      HeadNotInTail(e);
      assert e[0].0 !in Keys(RemoveKey(e[1..], k));
      DistinctConsIntro(e[0].0, Keys(RemoveKey(e[1..], k)));
    }
  }
}

lemma RemoveKeyLen(e: seq<(int, int)>, k: int)
  requires DistinctKeys(e)
  ensures k !in Keys(e) ==> RemoveKey(e, k) == e
  ensures k in Keys(e) ==> |RemoveKey(e, k)| == |e| - 1
{
  if |e| > 0 {
    KeysIndex(e);
    DistinctKeysTail(e);
    RemoveKeyLen(e[1..], k);
    if e[0].0 == k {
      HeadNotInTail(e);
    } else {
      assert RemoveKey(e, k) == [e[0]] + RemoveKey(e[1..], k);
      assert [e[0]] + e[1..] == e;
    }
  }
}

lemma AsMapRemoveKey(e: seq<(int, int)>, k: int)
  requires DistinctKeys(e)
  ensures AsMapOf(RemoveKey(e, k)) == AsMapOf(e) - {k}
{
  if |e| > 0 {
    KeysIndex(e);
    DistinctKeysTail(e);
    AsMapRemoveKey(e[1..], k);
    if e[0].0 == k {
      HeadNotInTail(e);
      AsMapMembership(e[1..], k);
      assert k !in AsMapOf(e[1..]);
    }
  }
}

// ---------------------------------------------------------------------------
// Prepend and drop-last
// ---------------------------------------------------------------------------

lemma AsMapPrepend(e: seq<(int, int)>, k: int, v: int)
  ensures AsMapOf([(k, v)] + e) == AsMapOf(e)[k := v]
{
  assert ([(k, v)] + e)[1..] == e;
}

lemma DistinctPrepend(e: seq<(int, int)>, k: int, v: int)
  requires DistinctKeys(e)
  requires k !in Keys(e)
  ensures DistinctKeys([(k, v)] + e)
{
  assert ([(k, v)] + e)[1..] == e;
  assert Keys([(k, v)] + e) == [k] + Keys(e);
  DistinctConsIntro(k, Keys(e));
}

lemma KeysPrefix(e: seq<(int, int)>, n: int)
  requires 0 <= n <= |e|
  ensures Keys(e[..n]) == Keys(e)[..n]
{
  KeysIndex(e);
  KeysIndex(e[..n]);
}

lemma DistinctDropLast(e: seq<(int, int)>)
  requires |e| > 0
  requires DistinctKeys(e)
  ensures DistinctKeys(e[..|e| - 1])
{
  KeysPrefix(e, |e| - 1);
  DistinctPrefix(Keys(e), |e| - 1);
}

lemma MapUpdateRemoveComm(M: map<int, int>, x: int, y: int, v: int)
  requires x != y
  ensures (M - {x})[y := v] == (M[y := v]) - {x}
{
}

lemma MapRemoveThenSet(M: map<int, int>, k: int, v: int)
  ensures (M - {k})[k := v] == M[k := v]
{
}

lemma MapRemoveReinsert(M: map<int, int>, k: int)
  requires k in M
  ensures (M - {k})[k := M[k]] == M
{
}

lemma AsMapDropLast(e: seq<(int, int)>)
  requires |e| > 0
  requires DistinctKeys(e)
  ensures AsMapOf(e[..|e| - 1]) == AsMapOf(e) - {e[|e| - 1].0}
{
  KeysIndex(e);
  if |e| == 1 {
    assert e[..0] == [];
  } else {
    DistinctKeysTail(e);
    var t := e[1..];
    assert t[|t| - 1] == e[|e| - 1];
    assert e[..|e| - 1] == [e[0]] + t[..|t| - 1];
    assert ([e[0]] + t[..|t| - 1])[1..] == t[..|t| - 1];
    AsMapDropLast(t);
    var x := e[|e| - 1].0;
    assert Keys(e)[0] == e[0].0 && Keys(e)[|e| - 1] == e[|e| - 1].0;
    assert e[0].0 != x;
    // AsMapOf(e[..|e|-1]) == AsMapOf(t[..|t|-1])[e[0].0 := e[0].1]
    //                     == (AsMapOf(t) - {x})[e[0].0 := e[0].1]
    assert AsMapOf(e[..|e| - 1]) == (AsMapOf(t) - {x})[e[0].0 := e[0].1];
    MapUpdateRemoveComm(AsMapOf(t), x, e[0].0, e[0].1);
    // == (AsMapOf(t)[e[0].0 := e[0].1]) - {x} == AsMapOf(e) - {x}
  }
}

// ---------------------------------------------------------------------------
// The cache
// ---------------------------------------------------------------------------

class LRUCache {
  const capacity: int
  var entries: seq<(int, int)>

  ghost predicate Valid()
    reads this
  {
    capacity >= 1 && |entries| <= capacity && DistinctKeys(entries)
  }

  constructor (cap: int)
    requires cap >= 1
    ensures Valid()
    ensures entries == []
    ensures AsMapOf(entries) == map[]
  {
    capacity := cap;
    entries := [];
  }

  method Get(key: int) returns (r: int)
    requires Valid()
    modifies this
    ensures Valid()
    ensures AsMapOf(entries) == old(AsMapOf(entries))
    ensures key in old(AsMapOf(entries)) ==>
              r == old(AsMapOf(entries))[key]
              && |entries| > 0 && entries[0] == (key, r)
              // the other entries keep their original relative order (just the
              // accessed key moved to the front)
              && entries[1..] == RemoveKey(old(entries), key)
    ensures key !in old(AsMapOf(entries)) ==> r == -1 && entries == old(entries)
  {
    AsMapMembership(entries, key);
    if key !in Keys(entries) {
      return -1;
    }
    ghost var old_e := entries;
    ValueOfIsMap(old_e, key);          // AsMapOf(old_e)[key] == ValueOf(old_e, key)
    r := ValueOf(entries, key);        // entries == old_e here, so r == AsMapOf(old_e)[key]

    var rest := RemoveKey(entries, key);
    RemoveKeyKeys(entries, key);
    RemoveKeyDistinct(entries, key);
    RemoveKeyLen(entries, key);        // |rest| == |old_e| - 1, so size is preserved
    DistinctPrepend(rest, key, r);
    entries := [(key, r)] + rest;

    // The abstract map is unchanged: rest == old map minus key, then key is
    // reinserted with its own value.
    AsMapRemoveKey(old_e, key);
    AsMapPrepend(rest, key, r);
    MapRemoveReinsert(AsMapOf(old_e), key);
  }

  method Put(key: int, value: int)
    requires Valid()
    modifies this
    ensures Valid()
    ensures |entries| > 0 && entries[0] == (key, value)
    ensures key in old(AsMapOf(entries)) ==>
              AsMapOf(entries) == old(AsMapOf(entries))[key := value]
    ensures key !in old(AsMapOf(entries)) && |old(entries)| < capacity ==>
              AsMapOf(entries) == old(AsMapOf(entries))[key := value]
    ensures key !in old(AsMapOf(entries)) && |old(entries)| == capacity ==>
              AsMapOf(entries) ==
              old(AsMapOf(entries))[key := value] - {old(entries)[|old(entries)| - 1].0}
    // order preservation: the surviving entries keep their original relative
    // order behind the new front element.
    ensures (key in old(AsMapOf(entries)) || |old(entries)| < capacity) ==>
              entries[1..] == RemoveKey(old(entries), key)
    ensures key !in old(AsMapOf(entries)) && |old(entries)| == capacity ==>
              entries[1..] == old(entries)[..|old(entries)| - 1]
  {
    ghost var old_e := entries;
    AsMapMembership(entries, key);

    var rest := RemoveKey(entries, key);
    RemoveKeyKeys(entries, key);
    RemoveKeyDistinct(entries, key);
    RemoveKeyLen(entries, key);
    DistinctPrepend(rest, key, value);
    var prepended := [(key, value)] + rest;
    AsMapRemoveKey(old_e, key);
    AsMapPrepend(rest, key, value);
    // AsMapOf(prepended) == (AsMapOf(old_e) - {key})[key := value] == AsMapOf(old_e)[key := value]
    MapRemoveThenSet(AsMapOf(old_e), key, value);

    if |prepended| > capacity {
      // Overflow: this branch is reached only when the key was absent and the
      // cache was full (otherwise |prepended| <= capacity), so rest == old_e and
      // exactly the least-recently-used entry (the back) is evicted.
      assert key !in Keys(old_e);
      assert rest == old_e;
      DistinctDropLast(prepended);
      AsMapDropLast(prepended);
      assert prepended[|prepended| - 1] == old_e[|old_e| - 1];
      entries := prepended[..|prepended| - 1];
    } else {
      entries := prepended;
    }
  }
}
