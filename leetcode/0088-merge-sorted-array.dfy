// Author: Shaobo He
// LeetCode 88: Merge Sorted Array (in-place merge from the back)

include "../lib/Seq.dfy"

import opened Seq

lemma SortedPrepend(x: int, xs: seq<int>)
  requires Sorted(xs)
  requires |xs| == 0 || x <= xs[0]
  ensures Sorted([x] + xs)
{
}

method PlaceFromNums1(nums1: array<int>, ghost orig: seq<int>, nums2: array<int>,
                      m: nat, n: nat, i: nat, j: nat, k: nat)
  requires nums1.Length == m + n
  requires nums2.Length == n
  requires |orig| == m
  requires 0 < i <= m && 0 < j <= n
  requires k == i + j
  requires nums1[..i] == orig[..i]
  requires Sorted(nums1[..i])
  requires Sorted(nums2[..])
  requires Sorted(nums1[k..])
  requires k == nums1.Length || nums1[i - 1] <= nums1[k]
  requires k == nums1.Length || nums2[j - 1] <= nums1[k]
  requires nums1[i - 1] >= nums2[j - 1]
  requires multiset(nums1[..i]) + multiset(nums2[..j]) + multiset(nums1[k..]) ==
           multiset(orig) + multiset(nums2[..])
  modifies nums1
  ensures nums1[..i - 1] == orig[..i - 1]
  ensures Sorted(nums1[..i - 1])
  ensures Sorted(nums2[..])
  ensures Sorted(nums1[k - 1..])
  ensures i - 1 == 0 || nums1[i - 2] <= nums1[k - 1]
  ensures nums2[j - 1] <= nums1[k - 1]
  ensures multiset(nums1[..i - 1]) + multiset(nums2[..j]) + multiset(nums1[k - 1..]) ==
          multiset(orig) + multiset(nums2[..])
{
  assert nums1[..i] == nums1[..i - 1] + [nums1[i - 1]];
  assert multiset(nums1[..i]) == multiset(nums1[..i - 1]) + multiset{nums1[i - 1]};
  assert i == 1 || nums1[i - 2] <= nums1[i - 1];
  nums1[k - 1] := nums1[i - 1];
  assert nums1[k - 1..] == [nums1[k - 1]] + nums1[k..];
  assert multiset(nums1[k - 1..]) == multiset{nums1[k - 1]} + multiset(nums1[k..]);
  SortedPrepend(nums1[k - 1], nums1[k..]);
}

method PlaceFromNums2(nums1: array<int>, ghost orig: seq<int>, nums2: array<int>,
                      m: nat, n: nat, i: nat, j: nat, k: nat)
  requires nums1.Length == m + n
  requires nums2.Length == n
  requires |orig| == m
  requires 0 <= i <= m && 0 < j <= n
  requires k == i + j
  requires nums1[..i] == orig[..i]
  requires Sorted(nums1[..i])
  requires Sorted(nums2[..])
  requires Sorted(nums1[k..])
  requires i == 0 || k == nums1.Length || nums1[i - 1] <= nums1[k]
  requires k == nums1.Length || nums2[j - 1] <= nums1[k]
  requires i == 0 || nums1[i - 1] < nums2[j - 1]
  requires multiset(nums1[..i]) + multiset(nums2[..j]) + multiset(nums1[k..]) ==
           multiset(orig) + multiset(nums2[..])
  modifies nums1
  ensures nums1[..i] == orig[..i]
  ensures Sorted(nums1[..i])
  ensures Sorted(nums2[..])
  ensures Sorted(nums1[k - 1..])
  ensures i == 0 || nums1[i - 1] <= nums1[k - 1]
  ensures j - 1 == 0 || nums2[j - 2] <= nums1[k - 1]
  ensures multiset(nums1[..i]) + multiset(nums2[..j - 1]) + multiset(nums1[k - 1..]) ==
          multiset(orig) + multiset(nums2[..])
{
  assert nums2[..j] == nums2[..j - 1] + [nums2[j - 1]];
  assert multiset(nums2[..j]) == multiset(nums2[..j - 1]) + multiset{nums2[j - 1]};
  nums1[k - 1] := nums2[j - 1];
  assert nums1[..i] == old(nums1[..i]);
  assert nums1[k..] == old(nums1[k..]);
  assert nums1[k - 1..] == [nums1[k - 1]] + nums1[k..];
  assert multiset(nums1[k - 1..]) == multiset{nums2[j - 1]} + multiset(old(nums1[k..]));
  calc {
    multiset(nums1[..i]) + multiset(nums2[..j - 1]) + multiset(nums1[k - 1..]);
    multiset(old(nums1[..i])) + multiset(nums2[..j - 1]) + (multiset{nums2[j - 1]} + multiset(old(nums1[k..])));
    multiset(old(nums1[..i])) + (multiset(nums2[..j - 1]) + multiset{nums2[j - 1]}) + multiset(old(nums1[k..]));
    multiset(old(nums1[..i])) + multiset(nums2[..j]) + multiset(old(nums1[k..]));
    multiset(orig) + multiset(nums2[..]);
  }
  SortedPrepend(nums1[k - 1], nums1[k..]);
}

method Merge(nums1: array<int>, m: nat, nums2: array<int>, n: nat)
  requires nums1.Length == m + n
  requires nums2.Length == n
  requires Sorted(nums1[..m])
  requires Sorted(nums2[..])
  modifies nums1
  ensures Sorted(nums1[..])
  ensures multiset(nums1[..]) == multiset(old(nums1[..m])) + multiset(nums2[..])
{
  ghost var orig := nums1[..m];
  var i, j, k := m, n, m + n;
  assert nums1[m + n..] == [];
  assert nums2[..n] == nums2[..];
  while j > 0
    invariant 0 <= i <= m && 0 <= j <= n
    invariant k == i + j
    invariant nums1[..i] == orig[..i]
    invariant Sorted(nums1[..i])
    invariant Sorted(nums1[k..])
    invariant Sorted(nums2[..])
    invariant i == 0 || k == nums1.Length || nums1[i - 1] <= nums1[k]
    invariant j == 0 || k == nums1.Length || nums2[j - 1] <= nums1[k]
    invariant multiset(nums1[..i]) + multiset(nums2[..j]) + multiset(nums1[k..]) ==
              multiset(orig) + multiset(nums2[..])
    decreases i + j
  {
    if i > 0 && nums1[i - 1] >= nums2[j - 1] {
      PlaceFromNums1(nums1, orig, nums2, m, n, i, j, k);
      i, k := i - 1, k - 1;
    } else {
      PlaceFromNums2(nums1, orig, nums2, m, n, i, j, k);
      j, k := j - 1, k - 1;
    }
  }
  assert nums1[..] == nums1[..i] + nums1[i..];
  forall p, q | 0 <= p < q < nums1.Length
    ensures nums1[p] <= nums1[q]
  {
    if q < i {
      assert nums1[..i][p] == nums1[p] && nums1[..i][q] == nums1[q];
    } else if p >= i {
      assert nums1[i..][p - i] == nums1[p] && nums1[i..][q - i] == nums1[q];
    } else {
      assert nums1[..i][p] == nums1[p];
      assert nums1[i..][q - i] == nums1[q];
    }
  }
}
