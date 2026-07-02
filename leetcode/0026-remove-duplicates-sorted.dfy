include "../lib/Seq.dfy"

import opened Seq

// {:vcs_split_on_every_assert} keeps each proof obligation in its own VC so the
// heavy forward-membership invariant and the reverse-membership proof do not
// compound into one VC that exceeds the time limit.
method {:vcs_split_on_every_assert} RemveDuplicates(nums: array<int>) returns (length: int)
  modifies nums
  requires 1 <= nums.Length
  requires Sorted(nums[..])
  ensures 1 <= length <= nums.Length
  ensures SortedStrict(nums[..length])
  ensures Distinct(nums[..length])
  ensures forall x :: x in old(nums[..]) ==> x in nums[..length]
  ensures forall x :: x in nums[..length] ==> x in old(nums[..])
{
  var j := 0;
  var i := 1;
  // src[k] is the original index that nums[k] was copied from -- an explicit
  // provenance witness, so the reverse-membership invariant has no existential.
  ghost var src := [0];
  while i < nums.Length
    invariant j < i <= nums.Length
    invariant nums[j + 1..] == old(nums[j + 1..])
    invariant SortedStrict(nums[..j + 1])
    invariant i < nums.Length ==> forall k :: 0 <= k < i ==> nums[k] <= nums[i]
    invariant forall k :: 0 <= k < i ==> old(nums[k]) in nums[..j + 1]
    invariant i < nums.Length ==> nums[j] <= nums[i]
    invariant |src| == j + 1
    invariant forall k :: 0 <= k <= j ==> 0 <= src[k] < nums.Length && nums[k] == old(nums[src[k]])
  {
    if nums[i] != nums[j] {
      assert nums[i] == old(nums[i]);
      j := j + 1;
      nums[j] := nums[i];
      src := src + [i];
      assert nums[..j + 1] == nums[..j] + [nums[i]];
    }
    i := i + 1;
  }
  length := j + 1;
  forall x | x in nums[..length]
    ensures x in old(nums[..])
  {
    var k :| 0 <= k < length && nums[..length][k] == x;
    assert nums[k] == old(nums[src[k]]) == old(nums[..])[src[k]];
  }
}