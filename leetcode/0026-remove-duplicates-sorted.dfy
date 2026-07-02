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
  // Both membership directions are witnessed by explicit index maps, so the
  // loop invariants are purely universal (no "x in seq" existential). The
  // {:trigger} pins stop Z3 from chasing the nested array selects through every
  // index (which otherwise blows up / destabilizes the solve time), and the two
  // existential steps are discharged by the isolated MembershipViaWitness lemma.
  //   src[k]: nums[k]      == old(nums[src[k]])   (kept values are original)
  //   fwd[k]: old(nums[k]) == nums[fwd[k]]        (originals are covered)
  ghost var src := [0];
  ghost var fwd := [0];
  while i < nums.Length
    invariant j < i <= nums.Length
    invariant nums[j + 1..] == old(nums[j + 1..])
    invariant SortedStrict(nums[..j + 1])
    invariant i < nums.Length ==> forall k :: 0 <= k < i ==> nums[k] <= nums[i]
    invariant i < nums.Length ==> nums[j] <= nums[i]
    invariant |src| == j + 1
    invariant forall k {:trigger src[k]} :: 0 <= k <= j ==>
                                              0 <= src[k] < nums.Length && nums[k] == old(nums[src[k]])
    invariant |fwd| == i
    invariant forall k {:trigger fwd[k]} :: 0 <= k < i ==>
                                              0 <= fwd[k] <= j && nums[fwd[k]] == old(nums[k])
  {
    assert nums[i] == old(nums[i]);
    if nums[i] != nums[j] {
      j := j + 1;
      nums[j] := nums[i];
      src := src + [i];
      fwd := fwd + [j];
      assert nums[..j + 1] == nums[..j] + [nums[i]];
    } else {
      fwd := fwd + [j];
    }
    i := i + 1;
  }
  length := j + 1;
  MembershipViaWitness(nums[..length], old(nums[..]), src);   // kept values are original
  MembershipViaWitness(old(nums[..]), nums[..length], fwd);   // originals are covered
}