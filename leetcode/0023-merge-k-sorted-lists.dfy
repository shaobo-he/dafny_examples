// Author: Shaobo He
// LeetCode 23: Merge k Sorted Lists
// Merge k ascending-sorted lists into one ascending-sorted list.

include "../lib/Seq.dfy"

import opened Seq

lemma SortedFirstMin(xs: seq<int>, z: int)
  requires Sorted(xs) && z in xs
  ensures xs[0] <= z
{
  var i :| 0 <= i < |xs| && xs[i] == z;
}

lemma SortedCons(x: int, xs: seq<int>)
  requires Sorted(xs)
  requires forall z :: z in xs ==> x <= z
  ensures Sorted([x] + xs)
{
  var r := [x] + xs;
  forall i, j | 0 <= i < j < |r|
    ensures r[i] <= r[j]
  {
    if i == 0 {
      assert r[j] == xs[j - 1];
      assert xs[j - 1] in xs;
    } else {
      assert r[i] == xs[i - 1];
      assert r[j] == xs[j - 1];
    }
  }
}

method Merge2(xs: seq<int>, ys: seq<int>) returns (r: seq<int>)
  requires Sorted(xs) && Sorted(ys)
  ensures Sorted(r)
  ensures multiset(r) == multiset(xs) + multiset(ys)
  decreases |xs| + |ys|
{
  if |xs| == 0 {
    return ys;
  }
  if |ys| == 0 {
    return xs;
  }
  if xs[0] <= ys[0] {
    var rest := Merge2(xs[1..], ys);
    forall z | z in rest
      ensures xs[0] <= z
    {
      assert multiset(rest) == multiset(xs[1..]) + multiset(ys);
      if z in xs[1..] {
        var i :| 0 <= i < |xs[1..]| && xs[1..][i] == z;
        assert xs[i + 1] == z;
      } else {
        assert multiset(rest)[z] >= 1;
        assert multiset(xs[1..])[z] == 0;
        assert multiset(ys)[z] >= 1;
        assert z in ys;
        SortedFirstMin(ys, z);
      }
    }
    SortedCons(xs[0], rest);
    r := [xs[0]] + rest;
    assert xs == [xs[0]] + xs[1..];
  } else {
    var rest := Merge2(xs, ys[1..]);
    forall z | z in rest
      ensures ys[0] <= z
    {
      assert multiset(rest) == multiset(xs) + multiset(ys[1..]);
      if z in xs {
        SortedFirstMin(xs, z);
      } else {
        assert multiset(rest)[z] >= 1;
        assert multiset(xs)[z] == 0;
        assert multiset(ys[1..])[z] >= 1;
        assert z in ys[1..];
        var i :| 0 <= i < |ys[1..]| && ys[1..][i] == z;
        assert ys[i + 1] == z;
      }
    }
    SortedCons(ys[0], rest);
    r := [ys[0]] + rest;
    assert ys == [ys[0]] + ys[1..];
  }
}

function MultisetSum(lists: seq<seq<int>>): multiset<int> {
  if |lists| == 0 then multiset{}
  else multiset(lists[0]) + MultisetSum(lists[1..])
}

method MergeK(lists: seq<seq<int>>) returns (r: seq<int>)
  requires forall i :: 0 <= i < |lists| ==> Sorted(lists[i])
  ensures Sorted(r)
  ensures multiset(r) == MultisetSum(lists)
  decreases |lists|
{
  if |lists| == 0 {
    return [];
  }
  var tail := MergeK(lists[1..]);
  r := Merge2(lists[0], tail);
}
