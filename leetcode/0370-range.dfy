include "../lib/Seq.dfy"

import opened Seq

function AddRange(xs: seq<int>, a: int, b: int, v: int): seq<int> {
  seq(|xs|, i requires 0 <= i < |xs| => xs[i] + if a <= i <= b then v else 0)
}

function PerformUpdates(xs: seq<int>, updates: seq<(int, int, int)>): seq<int>
  decreases updates
{
  if |updates| == 0 then
    xs
  else
    var (a, b, v) := updates[0];
    PerformUpdates(AddRange(xs, a, b, v), updates[1..])
}

lemma PerformUpdates1(xs: seq<int>, u: seq<(int, int, int)>)
  requires |u| > 0
  ensures PerformUpdates(xs, u) == PerformUpdates(PerformUpdates(xs, u[..|u| - 1]), [u[|u| - 1]])
  decreases |u|
{
  if |u| == 1 {
    assert u == [u[0]];
    assert u[..|u| - 1] == [];
  } else {
    var (a, b, v) := u[0];
    var xs' := AddRange(xs, a, b, v);
    // LHS = PerformUpdates(xs', u[1..])
    // Apply IH to u[1..]
    PerformUpdates1(xs', u[1..]);
    // IH: PerformUpdates(xs', u[1..]) == PerformUpdates(PerformUpdates(xs', u[1..][..|u[1..]| - 1]), [u[1..][|u[1..]| - 1]])
    assert u[1..][..|u[1..]| - 1] == u[1..|u| - 1];
    assert u[1..][|u[1..]| - 1] == u[|u| - 1];
    // So LHS == PerformUpdates(PerformUpdates(xs', u[1..|u|-1]), [u[|u|-1]])
    // Now RHS: PerformUpdates(PerformUpdates(xs, u[..|u|-1]), [u[|u|-1]])
    // unfold inner: u[..|u|-1] has length >= 1, first elt is u[0] = (a,b,v)
    assert u[..|u| - 1][0] == u[0];
    assert u[..|u| - 1][1..] == u[1..|u| - 1];
    // So PerformUpdates(xs, u[..|u|-1]) == PerformUpdates(AddRange(xs, a, b, v), u[1..|u|-1])
    //                                   == PerformUpdates(xs', u[1..|u|-1])
  }
}

// method AddRangeTest(xs: array<int>, a: int, b: int, v: int) returns (ys: array<int>)
//   requires 0 <= a <= b < xs.Length
//   ensures ys[..] == AddRange(xs[..], a, b, v)
// {
//   ys := new int[xs.Length];
//   forall i | 0 <= i < xs.Length {
//     ys[i] := xs[i];
//   }
//   assert ys[..] == xs[..];
//   var i := a;
//   while i <= b
//     invariant 0 <= i <= xs.Length
//     invariant ys[i..] == xs[i..]
//     invariant ys[..i] == AddRange(xs[..i], a, b, v)
//   {
//     ys[i] := ys[i] + v;
//     i := i + 1;
//   }
// }

method GetModifiedArraySimple(length: int, updates: array<(int, int, int)>) returns (arr: array<int>)
  requires 1 <= length
  requires forall k :: 0 <= k < updates.Length ==> 0 <= updates[k].0 <= updates[k].1 < length
  ensures arr.Length == length
  ensures arr[..] == PerformUpdates(seq(length, _ => 0), updates[..])
{
  arr := new int[length](_ => 0);
  ghost var s := seq(length, _ => 0);
  assert arr[..] == s;
  var k := 0;
  while k < updates.Length
    invariant 0 <= k <= updates.Length
    invariant arr[..] == s
    invariant s == PerformUpdates(seq(length, _ => 0), updates[..k])
  {
    var (a, b, v) := updates[k];
    ghost var vs := arr[..];
    ghost var us := updates[..k];
    s := AddRange(s, a, b, v);
    assert vs == PerformUpdates(seq(length, _ => 0), us);
    var i := a;
    while i <= b
      invariant a <= i <= b + 1
      invariant arr.Length == length
      invariant arr[i..] == vs[i..]
      invariant s == AddRange(vs, a, b, v)
      invariant arr[..i] == s[..i]
      invariant vs == PerformUpdates(seq(length, _ => 0), us)
      invariant updates[..k] == us
    {
      assert arr[i] == vs[i];
      assert s[i] == vs[i] + v;
      arr[i] := arr[i] + v;
      assert arr[i] == s[i];
      assert arr[..i + 1] == arr[..i] + [arr[i]];
      assert s[..i + 1] == s[..i] + [s[i]];
      i := i + 1;
    }
    assert vs == PerformUpdates(seq(length, _ => 0), us);
    assert s == PerformUpdates(vs, [updates[k]]);
    PerformUpdates1(seq(length, _ => 0), updates[..k + 1]);
    assert updates[..k + 1][..k] == us;
    assert updates[..k + 1][k] == updates[k];
    assert PerformUpdates(seq(length, _ => 0), updates[..k + 1][..k]) == vs;
    assert [updates[..k + 1][k]] == [updates[k]];
    k := k + 1;
  }
  assert updates[..] == updates[..updates.Length];
}