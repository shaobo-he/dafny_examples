include "../lib/Seq.dfy"

import opened Seq

// If every value in `vals` equals `pool` at a recorded index, then every value
// in `vals` occurs in `pool`. All existential reasoning is confined here, so the
// method below can carry purely universal (existential-free) loop invariants.
lemma MembershipViaWitness(vals: seq<int>, pool: seq<int>, w: seq<int>)
  requires |w| == |vals|
  requires forall k :: 0 <= k < |vals| ==> 0 <= w[k] < |pool| && vals[k] == pool[w[k]]
  ensures forall x :: x in vals ==> x in pool
{
  forall x | x in vals
    ensures x in pool
  {
    var k :| 0 <= k < |vals| && vals[k] == x;
    assert pool[w[k]] == x;
  }
}

method RemveDuplicates(nums: array<int>) returns (length: int)
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
  // src[k] records the original index nums[k] was copied from. The explicit
  // {:trigger src[k]} stops Z3 from chasing the nested array select through
  // every index, which is what blew up the solve time.
  ghost var src := [0];
  while i < nums.Length
    invariant j < i <= nums.Length
    invariant nums[j + 1..] == old(nums[j + 1..])
    invariant SortedStrict(nums[..j + 1])
    invariant i < nums.Length ==> forall k :: 0 <= k < i ==> nums[k] <= nums[i]
    invariant forall k :: 0 <= k < i ==> old(nums[k]) in nums[..j + 1]
    invariant i < nums.Length ==> nums[j] <= nums[i]
    invariant |src| == j + 1
    invariant forall k {:trigger src[k]} :: 0 <= k <= j ==>
                                              0 <= src[k] < nums.Length && nums[k] == old(nums[src[k]])
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
  MembershipViaWitness(nums[..length], old(nums[..]), src);
}